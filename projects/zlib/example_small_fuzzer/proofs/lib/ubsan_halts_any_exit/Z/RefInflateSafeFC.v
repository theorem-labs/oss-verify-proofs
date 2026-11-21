(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeFF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [dodist dolen fast_trip dodist_ok dolen_ok trip_ok].


Definition obrel (out : Z) (a b : arr) : Prop :=
  arr_len b = arr_len a /\ forall i, 0 <= i < out -> arr_get b i = arr_get a i.

Lemma obrel_refl : forall out a, obrel out a a.
Proof. intros. split; [reflexivity|intros; reflexivity]. Qed.
Lemma obrel_le : forall out out' a b, obrel out a b -> out' <= out -> obrel out' a b.
Proof. intros out out' a b [L E] H. split; [exact L|]. intros i Hi. apply E. lia. Qed.
Lemma obrel_set : forall out a b i v, obrel out a b -> 0 <= i -> obrel (i + 1) a b -> obrel (i + 1) (arr_set a i v) (arr_set b i v).
Proof.
  intros out a b i v [L E] Hi [_ E']. split; [rewrite !arr_len_set; exact L|].
  intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite L.
  destruct ((i =? j) && _); [reflexivity|]. apply E'. lia.
Qed.

Lemma fset_ob_id : forall f, fset_ob f (f_ob f) = f. Proof. intros []; reflexivity. Qed.
Lemma fpull_ob : forall x f ob, fpull x (fset_ob f ob) = fset_ob (fpull x f) ob. Proof. intros x [] ob; reflexivity. Qed.
Lemma fpull2_if_ob : forall x f ob, fpull2_if x (fset_ob f ob) = fset_ob (fpull2_if x f) ob.
Proof. intros x f ob. unfold fpull2_if. cbn [f_bits fset_ob]. destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]; cbn [f_bits]. destruct (a4 <? 15); [rewrite !fpull_ob|]; reflexivity. Qed.
Lemma fdrop_ob : forall f op ob, fdrop (fset_ob f ob) op = fset_ob (fdrop f op) ob. Proof. intros [] op ob; reflexivity. Qed.
Lemma fset_len_ob : forall f v ob, fset_len (fset_ob f ob) v = fset_ob (fset_len f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_dist_ob : forall f v ob, fset_dist (fset_ob f ob) v = fset_ob (fset_dist f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_op_ob : forall f v ob, fset_op (fset_ob f ob) v = fset_ob (fset_op f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_from_ob : forall f v ob, fset_from (fset_ob f ob) v = fset_ob (fset_from f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_ob_ob : forall f a b, fset_ob (fset_ob f a) b = fset_ob f b. Proof. intros [] a b; reflexivity. Qed.
Lemma f_ob_fset_ob : forall f ob, f_ob (fset_ob f ob) = ob. Proof. intros [] ob; reflexivity. Qed.
Lemma scal_ob : forall f ob,
  f_in (fset_ob f ob) = f_in f /\ f_out (fset_ob f ob) = f_out f /\ f_hold (fset_ob f ob) = f_hold f /\ f_bits (fset_ob f ob) = f_bits f
  /\ f_len (fset_ob f ob) = f_len f /\ f_dist (fset_ob f ob) = f_dist f /\ f_op (fset_ob f ob) = f_op f /\ f_from (fset_ob f ob) = f_from f.
Proof. intros [] ob; repeat split; reflexivity. Qed.

Ltac obn := rewrite ?fpull_ob, ?fpull2_if_ob, ?fdrop_ob, ?fset_len_ob, ?fset_dist_ob, ?fset_op_ob, ?fset_from_ob, ?fset_ob_ob, ?f_ob_fset_ob.
Ltac obs f ob := let H := fresh in pose proof (scal_ob f ob) as H;
  rewrite ?(proj1 H), ?(proj1 (proj2 H)), ?(proj1 (proj2 (proj2 H))), ?(proj1 (proj2 (proj2 (proj2 H)))),
          ?(proj1 (proj2 (proj2 (proj2 (proj2 H))))), ?(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))),
          ?(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))), ?(proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) in *; clear H.


Definition fromOK (f : ffs) : Prop := forall i, f_from f = FOut i -> 0 <= i < f_out f.

Definition OBR (f : ffs) (g : ffs) : Prop := exists ob, g = fset_ob f ob /\ obrel (f_out f) (f_ob f) ob.
Definition OBRF (f : ffs) (g : ffs) : Prop := OBR f g /\ fromOK f.

Lemma cp1_rel : forall x f g, OBRF f g -> 0 <= f_out f < arr_len (f_ob f) ->
  OBRF (cp1 x f) (cp1 x g) /\ arr_len (f_ob (cp1 x f)) = arr_len (f_ob f) /\ f_out (cp1 x f) = f_out f + 1.
Proof.
  intros x f g [(ob & -> & [L E]) FK] Ho. unfold OBRF, OBR, obrel, fromOK, cp1 in *.
  destruct f as [fi fo fh fb fl fd fp fr fob]. facc. revert L E FK Ho. facc. intros L E FK Ho.
  assert (V : match fr with FWin i => arr_get (x_window x) i | FOut i => arr_get ob i end
            = match fr with FWin i => arr_get (x_window x) i | FOut i => arr_get fob i end).
  { destruct fr as [i|i]; [reflexivity|]. apply E. apply (FK i eq_refl). }
  rewrite V. set (v := match fr with FWin i => _ | FOut i => _ end). clearbody v.
  split; [|split; [apply arr_len_set | reflexivity]].
  facc. split.
  - exists (arr_set ob fo v). split; [reflexivity|].
    split; [rewrite !arr_len_set; exact L|]. intros j Hj.
    rewrite !arr_get_set. unfold arr_inb. rewrite L.
    destruct (Z.eqb_spec fo j) as [<-|NE]; cbn [andb].
    + rewrite (proj2 (Z.leb_le 0 fo)) by lia. rewrite (proj2 (Z.ltb_lt fo _)) by lia. reflexivity.
    + apply E. lia.
  - intros i Ei. destruct fr as [i0|i0]; cbn [from_succ] in Ei; [discriminate Ei|].
    injection Ei; intros <-. specialize (FK i0 eq_refl). lia.
Qed.

Lemma cpn_rel : forall x n f g, OBRF f g -> 0 <= f_out f -> f_out f + Z.of_nat n <= arr_len (f_ob f) ->
  OBRF (cpn x n f) (cpn x n g) /\ arr_len (f_ob (cpn x n f)) = arr_len (f_ob f) /\ f_out (cpn x n f) = f_out f + Z.of_nat n.
Proof.
  intros x n. induction n as [|n IH]; intros f g H Ho Hn.
  - cbn [cpn Z.of_nat]. split; [exact H|]. split; [reflexivity|lia].
  - cbn [cpn]. rewrite Nat2Z.inj_succ in Hn.
    destruct (cp1_rel x f g H ltac:(lia)) as (H1 & L1 & O1).
    destruct (IH (cp1 x f) (cp1 x g) H1 ltac:(lia) ltac:(rewrite L1, O1; lia)) as (H2 & L2 & O2).
    split; [exact H2|]. rewrite L2, O2, L1, O1, Nat2Z.inj_succ. split; [reflexivity|lia].
Qed.

Lemma OBR_scal : forall f g (h : ffs -> ffs),
  (forall f0 ob, h (fset_ob f0 ob) = fset_ob (h f0) ob) ->
  (forall f0, f_out (h f0) = f_out f0 /\ f_ob (h f0) = f_ob f0 /\ f_from (h f0) = f_from f0) ->
  OBR f g -> OBR (h f) (h g).
Proof.
  intros f g h Hc Hk (ob & -> & R). rewrite Hc. destruct (Hk f) as (E1 & E2 & E3).
  exists ob. split; [reflexivity|]. rewrite E1, E2. exact R.
Qed.
Lemma OBRF_scal : forall f g (h : ffs -> ffs),
  (forall f0 ob, h (fset_ob f0 ob) = fset_ob (h f0) ob) ->
  (forall f0, f_out (h f0) = f_out f0 /\ f_ob (h f0) = f_ob f0 /\ f_from (h f0) = f_from f0) ->
  OBRF f g -> OBRF (h f) (h g).
Proof.
  intros f g h Hc Hk [H FK]. split; [exact (OBR_scal f g h Hc Hk H)|].
  destruct (Hk f) as (E1 & E2 & E3). intros i Ei. rewrite E3 in Ei. rewrite E1. exact (FK i Ei).
Qed.
Lemma OBRF_fset_len : forall f g v, OBRF f g -> OBRF (fset_len f v) (fset_len g v).
Proof. intros f g v. apply (OBRF_scal f g (fun f0 => fset_len f0 v)); [intros; apply fset_len_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBRF_fset_op : forall f g v, OBRF f g -> OBRF (fset_op f v) (fset_op g v).
Proof. intros f g v. apply (OBRF_scal f g (fun f0 => fset_op f0 v)); [intros; apply fset_op_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fpull : forall x f g, OBR f g -> OBR (fpull x f) (fpull x g).
Proof. intros x f g. apply OBR_scal; [intros; apply fpull_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fpull2_if : forall x f g, OBR f g -> OBR (fpull2_if x f) (fpull2_if x g).
Proof.
  intros x f g H. pose proof H as (ob & E & _). unfold fpull2_if. rewrite E. cbn [f_bits fset_ob].
  destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]; cbn [f_bits]. rewrite <- E.
  destruct (a4 <? 15); [apply OBR_fpull; apply OBR_fpull; exact H | exact H].
Qed.
Lemma OBR_fdrop : forall f g op, OBR f g -> OBR (fdrop f op) (fdrop g op).
Proof. intros f g op. apply (OBR_scal f g (fun f0 => fdrop f0 op)); [intros; apply fdrop_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fset_len : forall f g v, OBR f g -> OBR (fset_len f v) (fset_len g v).
Proof. intros f g v. apply (OBR_scal f g (fun f0 => fset_len f0 v)); [intros; apply fset_len_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fset_dist : forall f g v, OBR f g -> OBR (fset_dist f v) (fset_dist g v).
Proof. intros f g v. apply (OBR_scal f g (fun f0 => fset_dist f0 v)); [intros; apply fset_dist_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fset_op : forall f g v, OBR f g -> OBR (fset_op f v) (fset_op g v).
Proof. intros f g v. apply (OBR_scal f g (fun f0 => fset_op f0 v)); [intros; apply fset_op_ob | intros []; repeat split; reflexivity]. Qed.
Lemma OBR_fset_from : forall f g v, OBR f g -> (forall i, v = FOut i -> 0 <= i < f_out f) -> OBRF (fset_from f v) (fset_from g v).
Proof.
  intros f g v (ob & -> & R) Hv. rewrite fset_from_ob. split.
  - exists ob. split; [reflexivity|]. destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]; cbn [f_out f_ob fset_from] in *. exact R.
  - unfold fromOK. destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]; cbn [f_out f_ob f_from fset_from] in *. intros i Ei. exact (Hv i Ei).
Qed.
Lemma OBRF_OBR : forall f g, OBRF f g -> OBR f g.
Proof. intros f g [H _]. exact H. Qed.

Lemma OBR_eq : forall f g, OBR f g -> exists ob, g = fset_ob f ob.
Proof. intros f g (ob & E & _). exists ob. exact E. Qed.
Lemma OBRF_eq : forall f g, OBRF f g -> exists ob, g = fset_ob f ob.
Proof. intros f g [(ob & E & _) _]. exists ob. exact E. Qed.


Lemma OBR_len : forall f g, OBR f g -> arr_len (f_ob g) = arr_len (f_ob f).
Proof. intros f g (ob & -> & [L _]). rewrite f_ob_fset_ob. exact L. Qed.

Lemma copy_op_rel : forall x f g, OBRF f g -> 1 <= f_op f < 2 ^ 32 -> 0 <= f_out f -> f_out f + f_op f <= arr_len (f_ob f) ->
  OBRF (copy_op x f) (copy_op x g) /\ arr_len (f_ob (copy_op x f)) = arr_len (f_ob f) /\ f_out (copy_op x f) = f_out f + f_op f
  /\ f_len (copy_op x f) = f_len f /\ f_dist (copy_op x f) = f_dist f.
Proof.
  intros x f g H Hop Ho Hroom. destruct (OBRF_eq f g H) as [ob Eg].
  rewrite (copy_op_cpn x g) by (rewrite Eg; obs f ob; exact Hop). rewrite (copy_op_cpn x f) by exact Hop.
  replace (f_op g) with (f_op f) by (rewrite Eg; obs f ob; reflexivity).
  destruct (cpn_rel x (Z.to_nat (f_op f)) f g H Ho ltac:(lia)) as (H1 & L1 & O1).
  destruct (cpn_keep x (Z.to_nat (f_op f)) f) as (_ & _ & _ & KL & KD & _).
  split; [apply OBRF_fset_op; exact H1|]. facc. rewrite L1, O1, KL, KD. repeat split; lia.
Qed.

Lemma copy_while3_rel : forall x f g, OBRF f g -> 0 <= f_len f < 2 ^ 32 -> 0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) ->
  OBRF (copy_while3 x f) (copy_while3 x g) /\ arr_len (f_ob (copy_while3 x f)) = arr_len (f_ob f)
  /\ 0 <= f_out (copy_while3 x f) /\ f_out (copy_while3 x f) + f_len (copy_while3 x f) <= arr_len (f_ob f) /\ 0 <= f_len (copy_while3 x f) <= 2.
Proof.
  intros x f g H Hlen Ho Hroom. destruct (OBRF_eq f g H) as [ob Eg].
  rewrite (copy_while3_cpn x g) by (rewrite Eg; obs f ob; exact Hlen). rewrite (copy_while3_cpn x f) by exact Hlen.
  replace (f_len g) with (f_len f) by (rewrite Eg; obs f ob; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM. pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  destruct (cpn_rel x (Z.to_nat (3 * (f_len f / 3))) f g H Ho ltac:(lia)) as (H1 & L1 & O1).
  split; [apply OBRF_fset_len; exact H1|]. facc. rewrite L1, O1. repeat split; lia.
Qed.

Lemma copy_do3_rel : forall x f g, OBRF f g -> 3 <= f_len f < 2 ^ 32 -> 0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) ->
  OBRF (copy_do3 x f) (copy_do3 x g) /\ arr_len (f_ob (copy_do3 x f)) = arr_len (f_ob f)
  /\ 0 <= f_out (copy_do3 x f) /\ f_out (copy_do3 x f) + f_len (copy_do3 x f) <= arr_len (f_ob f) /\ 0 <= f_len (copy_do3 x f) <= 2.
Proof.
  intros x f g H Hlen Ho Hroom. destruct (OBRF_eq f g H) as [ob Eg].
  rewrite (copy_do3_cpn x g) by (rewrite Eg; obs f ob; exact Hlen). rewrite (copy_do3_cpn x f) by exact Hlen.
  replace (f_len g) with (f_len f) by (rewrite Eg; obs f ob; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM. pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  destruct (cpn_rel x (Z.to_nat (3 * (f_len f / 3))) f g H Ho ltac:(lia)) as (H1 & L1 & O1).
  split; [apply OBRF_fset_len; exact H1|]. facc. rewrite L1, O1. repeat split; lia.
Qed.

Lemma copy_tail_rel : forall x f g, OBRF f g -> 0 <= f_len f <= 2 -> 0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) ->
  OBRF (copy_tail x f) (copy_tail x g) /\ arr_len (f_ob (copy_tail x f)) = arr_len (f_ob f).
Proof.
  intros x f g H Hlen Ho Hroom. destruct (OBRF_eq f g H) as [ob Eg].
  rewrite (copy_tail_cpn x g) by (rewrite Eg; obs f ob; exact Hlen). rewrite (copy_tail_cpn x f) by exact Hlen.
  replace (f_len g) with (f_len f) by (rewrite Eg; obs f ob; reflexivity).
  destruct (cpn_rel x (Z.to_nat (f_len f)) f g H Ho ltac:(lia)) as (H1 & L1 & O1).
  split; [exact H1|exact L1].
Qed.

Lemma dist_tailcopy_rel : forall x f g, OBRF f g -> 0 <= f_len f < 2 ^ 32 -> 0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) ->
  OBRF (dist_tailcopy x f) (dist_tailcopy x g) /\ arr_len (f_ob (dist_tailcopy x f)) = arr_len (f_ob f).
Proof.
  intros x f g H Hlen Ho Hroom. unfold dist_tailcopy.
  destruct (copy_while3_rel x f g H Hlen Ho Hroom) as (H1 & L1 & O1 & R1 & M1).
  destruct (copy_tail_rel x _ _ H1 M1 O1 ltac:(rewrite L1; exact R1)) as (H2 & L2).
  split; [exact H2|]. rewrite L2. exact L1.
Qed.

Lemma out_copy_rel : forall x f g, OBR f g -> 3 <= f_len f < 2 ^ 32 -> 0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) ->
  1 <= f_dist f <= f_out f ->
  OBR (out_copy x f) (out_copy x g) /\ arr_len (f_ob (out_copy x f)) = arr_len (f_ob f).
Proof.
  intros x f g H Hlen Ho Hroom Hd. unfold out_copy.
  destruct (OBR_eq f g H) as [ob Eg].
  replace (f_out g - f_dist g) with (f_out f - f_dist f) by (rewrite Eg; obs f ob; reflexivity).
  assert (H0 : OBRF (fset_from f (FOut (f_out f - f_dist f))) (fset_from g (FOut (f_out f - f_dist f)))).
  { apply OBR_fset_from; [exact H|]. intros i Ei. injection Ei; intros <-. lia. }
  destruct (copy_do3_rel x _ _ H0 ltac:(facc; exact Hlen) ltac:(facc; exact Ho) ltac:(facc; exact Hroom)) as (H1 & L1 & O1 & R1 & M1).
  revert L1 R1. facc. intros L1 R1.
  destruct (copy_tail_rel x _ _ H1 M1 O1 ltac:(rewrite L1; exact R1)) as (H2 & L2).
  split; [exact (OBRF_OBR _ _ H2)|]. rewrite L2. exact L1.
Qed.

Lemma win_place_rel : forall x f g, OBR f g -> 1 <= f_op f < 2 ^ 32 -> 0 <= f_len f < 2 ^ 32 -> 0 <= x_wnext x ->
  0 <= f_out f -> f_out f + f_len f <= arr_len (f_ob f) -> 1 <= f_dist f <= f_out f + f_op f ->
  OBRF (win_place x f) (win_place x g) /\ arr_len (f_ob (win_place x f)) = arr_len (f_ob f)
  /\ f_out f <= f_out (win_place x f) /\ 0 <= f_len (win_place x f) < 2 ^ 32
  /\ f_out (win_place x f) + f_len (win_place x f) <= arr_len (f_ob f).
Proof.
  intros x f g H Hop Hlen Hwn Ho Hroom Hd. destruct (OBR_eq f g H) as [ob Eg]. unfold win_place. facc.
  rewrite Eg. obs f ob. rewrite <- Eg.
  Ltac wfin H := split; [exact H|]; facc.
  destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0].
  - destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
    + set (f1 := fset_len (fset_from f (FWin (x_wsize x - f_op f))) (wrap32 (f_len f - f_op f))).
      set (g1 := fset_len (fset_from g (FWin (x_wsize x - f_op f))) (wrap32 (f_len f - f_op f))).
      assert (H1 : OBRF f1 g1) by (subst f1 g1; apply OBRF_fset_len; apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]).
      assert (E1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f /\ f_out f1 = f_out f /\ f_ob f1 = f_ob f /\ f_dist f1 = f_dist f)
        by (subst f1; facc; rewrite wrap32_id by lia; repeat split; reflexivity).
      destruct E1 as (Eo & El & Eout & Eob & Ed).
      destruct (copy_op_rel x f1 g1 H1 ltac:(rewrite Eo; lia) ltac:(rewrite Eout; lia) ltac:(rewrite Eout, Eo, Eob; lia)) as (H2 & L2 & O2 & L2' & D2).
      pose proof (OBRF_eq _ _ H2) as [ob2 Eg2]. rewrite Eg2. obs (copy_op x f1) ob2. rewrite <- Eg2.
      split; [|facc; rewrite L2, O2, L2', Eout, Eo, El, Eob; lia].
      apply OBR_fset_from; [exact (OBRF_OBR _ _ H2)|]. intros i Ei. injection Ei; intros <-. rewrite O2, D2, Eout, Eo, Ed. lia.
    + split; [apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]|]. facc. lia.
  - destruct (Z.ltb_spec (x_wnext x) (f_op f)) as [Cw|Cw].
    + rewrite (wrap32_id (f_op f - x_wnext x)) by lia.
      destruct (Z.ltb_spec (f_op f - x_wnext x) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_op (fset_from f (FWin (x_wsize x + x_wnext x - f_op f))) (f_op f - x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x)))).
        set (g1 := fset_len (fset_op (fset_from g (FWin (x_wsize x + x_wnext x - f_op f))) (f_op f - x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x)))).
        assert (H1 : OBRF f1 g1) by (subst f1 g1; apply OBRF_fset_len; apply OBRF_fset_op; apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]).
        assert (E1 : f_op f1 = f_op f - x_wnext x /\ f_len f1 = f_len f - (f_op f - x_wnext x) /\ f_out f1 = f_out f /\ f_ob f1 = f_ob f /\ f_dist f1 = f_dist f)
          by (subst f1; facc; rewrite wrap32_id by lia; repeat split; reflexivity).
        destruct E1 as (Eo & El & Eout & Eob & Ed).
        destruct (copy_op_rel x f1 g1 H1 ltac:(rewrite Eo; lia) ltac:(rewrite Eout; lia) ltac:(rewrite Eout, Eo, Eob; lia)) as (H2 & L2 & O2 & L2' & D2).
        pose proof (OBRF_eq _ _ H2) as [ob2 Eg2].
        assert (H3 : OBRF (fset_from (copy_op x f1) (FWin 0)) (fset_from (copy_op x g1) (FWin 0))) by (apply OBR_fset_from; [exact (OBRF_OBR _ _ H2) | intros i Ei; discriminate Ei]).
        rewrite Eg2. obs (copy_op x f1) ob2. rewrite <- Eg2. rewrite L2', El.
        destruct (Z.ltb_spec (x_wnext x) (f_len f - (f_op f - x_wnext x))) as [C2|C2].
        -- set (f3 := fset_len (fset_op (fset_from (copy_op x f1) (FWin 0)) (x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x) - x_wnext x))).
           set (g3 := fset_len (fset_op (fset_from (copy_op x g1) (FWin 0)) (x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x) - x_wnext x))).
           assert (H4 : OBRF f3 g3) by (subst f3 g3; apply OBRF_fset_len; apply OBRF_fset_op; exact H3).
           assert (E3 : f_op f3 = x_wnext x /\ f_len f3 = f_len f - (f_op f - x_wnext x) - x_wnext x /\ f_out f3 = f_out f + (f_op f - x_wnext x)
                        /\ arr_len (f_ob f3) = arr_len (f_ob f) /\ f_dist f3 = f_dist f)
             by (subst f3; facc; rewrite wrap32_id by lia; rewrite O2, L2, D2, Eout, Eo, Eob, Ed; repeat split; reflexivity).
           destruct E3 as (Eo3 & El3 & Eout3 & Eob3 & Ed3).
           destruct (copy_op_rel x f3 g3 H4 ltac:(rewrite Eo3; lia) ltac:(rewrite Eout3; lia) ltac:(rewrite Eout3, Eo3, Eob3; lia)) as (H5 & L5 & O5 & L5' & D5).
           pose proof (OBRF_eq _ _ H5) as [ob5 Eg5]. rewrite Eg5. obs (copy_op x f3) ob5. rewrite <- Eg5.
           split; [|facc; rewrite L5, O5, L5', Eout3, Eo3, El3, Eob3; lia].
           apply OBR_fset_from; [exact (OBRF_OBR _ _ H5)|]. intros i Ei. injection Ei; intros <-. rewrite O5, D5, Eout3, Eo3, Ed3. lia.
        -- split; [exact H3|]. facc. rewrite L2, O2, L2', Eout, Eo, El, Eob. lia.
      * split; [apply OBRF_fset_op; apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]|]. facc. lia.
    + destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_from f (FWin (x_wnext x - f_op f))) (wrap32 (f_len f - f_op f))).
        set (g1 := fset_len (fset_from g (FWin (x_wnext x - f_op f))) (wrap32 (f_len f - f_op f))).
        assert (H1 : OBRF f1 g1) by (subst f1 g1; apply OBRF_fset_len; apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]).
        assert (E1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f /\ f_out f1 = f_out f /\ f_ob f1 = f_ob f /\ f_dist f1 = f_dist f)
          by (subst f1; facc; rewrite wrap32_id by lia; repeat split; reflexivity).
        destruct E1 as (Eo & El & Eout & Eob & Ed).
        destruct (copy_op_rel x f1 g1 H1 ltac:(rewrite Eo; lia) ltac:(rewrite Eout; lia) ltac:(rewrite Eout, Eo, Eob; lia)) as (H2 & L2 & O2 & L2' & D2).
        pose proof (OBRF_eq _ _ H2) as [ob2 Eg2]. rewrite Eg2. obs (copy_op x f1) ob2. rewrite <- Eg2.
        split; [|facc; rewrite L2, O2, L2', Eout, Eo, El, Eob; lia].
        apply OBR_fset_from; [exact (OBRF_OBR _ _ H2)|]. intros i Ei. injection Ei; intros <-. rewrite O2, D2, Eout, Eo, Ed. lia.
      * split; [apply OBR_fset_from; [exact H | intros i Ei; discriminate Ei]|]. facc. lia.
Qed.


Definition RREL (ON lo : Z) (r1 r2 : InflateFast.fstep) : Prop :=
  match r1, r2 with
  | FCont f1, FCont f2 => OBR f1 f2 /\ lo <= f_out f1 /\ arr_len (f_ob f1) = ON
  | FBreak f1 m1 g1, FBreak f2 m2 g2 => OBR f1 f2 /\ lo <= f_out f1 /\ arr_len (f_ob f1) = ON /\ m2 = m1 /\ g2 = g1
  | _, _ => False
  end.

Definition dpulls (x : ffx) (e : Z) (f : ffs) : ffs :=
  if f_bits f <? e then (if f_bits (fpull x f) <? e then fpull x (fpull x f) else fpull x f) else f.
Definition dext (x : ffx) (e : Z) (f : ffs) : ffs :=
  let f := dpulls x e f in
  fdrop (fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask e)))) e.
Lemma dpulls_ob : forall x e f ob, dpulls x e (fset_ob f ob) = fset_ob (dpulls x e f) ob.
Proof. intros x e f ob. unfold dpulls. obs f ob. rewrite !fpull_ob. obs (fpull x f) ob. destruct (f_bits f <? e); [destruct (f_bits (fpull x f) <? e)|]; reflexivity. Qed.
Lemma dext_ob : forall x e f ob, dext x e (fset_ob f ob) = fset_ob (dext x e f) ob.
Proof. intros x e f ob. unfold dext. rewrite dpulls_ob. obs (dpulls x e f) ob. rewrite fset_dist_ob, fdrop_ob. reflexivity. Qed.
Lemma OBR_dpulls : forall x e f g, OBR f g -> OBR (dpulls x e f) (dpulls x e g) /\ f_out (dpulls x e f) = f_out f /\ f_ob (dpulls x e f) = f_ob f.
Proof.
  intros x e f g H. destruct (OBR_eq f g H) as [ob ->]. rewrite dpulls_ob. unfold dpulls.
  destruct (f_bits f <? e); [destruct (f_bits (fpull x f) <? e)|].
  - split; [rewrite <- !fpull_ob; apply OBR_fpull; apply OBR_fpull; exact H | destruct f; split; reflexivity].
  - split; [rewrite <- !fpull_ob; apply OBR_fpull; exact H | destruct f; split; reflexivity].
  - split; [exact H | split; reflexivity].
Qed.
Lemma OBR_dext : forall x e f g, OBR f g -> OBR (dext x e f) (dext x e g) /\ f_out (dext x e f) = f_out f /\ f_ob (dext x e f) = f_ob f.
Proof.
  intros x e f g H. destruct (OBR_dpulls x e f g H) as (H1 & E1 & E2). unfold dext. cbv zeta.
  destruct (OBR_eq _ _ H1) as [ob1 Eg1]. rewrite Eg1 in H1 |- *. obs (dpulls x e f) ob1.
  split; [apply OBR_fdrop; apply OBR_fset_dist; exact H1|]. rewrite <- E1, <- E2. destruct (dpulls x e f); split; reflexivity.
Qed.

Lemma dodist_S2 : forall k x s here f,
  dodist (S k) x s here f =
    let b := code_bits here in
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let e := Z.land op 15 in
      let f3 := dext x e (fset_dist (fdrop f b) (code_val here)) in
      let opd := wrap32 (f_out f3 - x_beg x) in
      if opd <? f_dist f3 then
        let opw := wrap32 (f_dist f3 - opd) in
        if (x_whave x <? opw) && negb (x_sane x =? 0)
        then FBreak (fset_op f3 opw) BAD (Some MSG_invalid_distance_too_far_back)
        else FCont (dist_tailcopy x (win_place x (fset_op f3 opw)))
      else FCont (out_copy x f3)
    else if Z.land op 64 =? 0 then
      dodist k x s (code_at s (is_distcode s) (code_val here + Z.land (f_hold (fdrop f b)) (zmask op))) (fdrop f b)
    else FBreak (fdrop f b) BAD (Some MSG_invalid_distance_code).
Proof. intros. rewrite dodist_S. unfold dext, dpulls. reflexivity. Qed.

Lemma dodist_ok_S2 : forall x s IN ON WN k here f,
  dodist_ok x s IN ON WN (S k) here f =
    let b := code_bits here in
    (b <=? f_bits f) &&
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let f1 := fset_dist (fdrop f b) (code_val here) in
      let e := Z.land op 15 in
      (if f_bits f1 <? e then (f_in f1 + 1 <=? IN) && (if f_bits f1 + 8 <? e then f_in f1 + 2 <=? IN else true) else true) &&
      ((e <=? f_bits (dpulls x e f1)) &&
      let f3 := dext x e f1 in
      (1 <=? f_dist f3) && (3 <=? f_len f3) && (f_out f3 + f_len f3 <=? ON) &&
      let opd := wrap32 (f_out f3 - x_beg x) in
      if opd <? f_dist f3 then
        let opw := wrap32 (f_dist f3 - opd) in
        if (x_whave x <? opw) && negb (x_sane x =? 0) then true
        else window_ok x ON WN (fset_op f3 opw)
      else true)
    else if Z.land op 64 =? 0 then
      (op <? 16) &&
      let i := code_val here + Z.land (f_hold (fdrop f b)) (zmask op) in
      (i <? ctab_len (is_distcode s)) && dodist_ok x s IN ON WN k (code_at s (is_distcode s) i) (fdrop f b)
    else true.
Proof. intros. rewrite dodist_ok_S. unfold dext, dpulls. reflexivity. Qed.

Section B.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

  Lemma dodist_relB : forall k here f g,
    OBR f g -> x_beg x <= f_out f -> arr_len (f_ob f) = ON ->
    dodist_ok x s IN ON WN k here f = true ->
    RREL ON (x_beg x) (dodist k x s here f) (dodist k x s here g).
  Proof.
    induction k as [|k IH]; intros here f g H Hbeg HL Hok; [discriminate Hok|].
    destruct (OBR_eq f g H) as [ob Eg].
    rewrite dodist_ok_S2 in Hok. rewrite !dodist_S2. cbv zeta in Hok. cbv zeta.
    apply andb_prop in Hok as [B1 Hok].
    assert (Hd : OBR (fdrop f (code_bits here)) (fdrop g (code_bits here))) by (apply OBR_fdrop; exact H).
    destruct (negb (Z.land (code_op here) 16 =? 0)).
    - set (e := Z.land (code_op here) 15) in *.
      set (f1 := fset_dist (fdrop f (code_bits here)) (code_val here)) in *.
      destruct (OBR_dext x e f1 (fset_dist (fdrop g (code_bits here)) (code_val here)) ltac:(subst f1; apply OBR_fset_dist; exact Hd)) as (H3 & E3o & E3ob).
      destruct (OBR_eq _ _ H3) as [ob3 Eg3]. rewrite Eg3.
      set (f3 := dext x e f1) in *. obs f3 ob3.
      assert (E3o' : f_out f3 = f_out f) by (rewrite E3o; subst f1; destruct f; reflexivity).
      assert (E3ob' : f_ob f3 = f_ob f) by (rewrite E3ob; subst f1; destruct f; reflexivity).
      apply andb_prop in Hok as [B2 Hok]. apply andb_prop in Hok as [B3 Hok].
      apply andb_prop in Hok as [B4 Hok]. apply andb_prop in B4 as [B4 B6]. apply andb_prop in B4 as [B4 B5].
      apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6.
      set (opd := wrap32 (f_out f3 - x_beg x)) in *.
      assert (Hopd : 0 <= opd <= f_out f3 - x_beg x).
      { subst opd. rewrite wrap32_mod. pose proof (Z.mod_pos_bound (f_out f3 - x_beg x) (2 ^ 32) ltac:(lia)).
        pose proof (Z.mod_le (f_out f3 - x_beg x) (2 ^ 32) ltac:(rewrite E3o'; lia) ltac:(lia)). lia. }
      assert (Hd32 : 0 <= f_dist f3 < 2 ^ 32).
      { subst f3. unfold dext. cbv zeta. facc. apply wrap32_range. }
      destruct (Z.ltb_spec opd (f_dist f3)) as [Cw|Cw].
      + rewrite (wrap32_id (f_dist f3 - opd)) in * by lia.
        destruct ((x_whave x <? f_dist f3 - opd) && negb (x_sane x =? 0)).
        * cbn [RREL]. rewrite <- Eg3. split; [apply OBR_fset_op; exact H3|]. facc. rewrite E3o', E3ob'. repeat split; first [lia | exact HL | reflexivity].
        * cbn [RREL]. rewrite <- Eg3.
          destruct (win_place_rel x (fset_op f3 (f_dist f3 - opd)) (fset_op (dext x e (fset_dist (fdrop g (code_bits here)) (code_val here))) (f_dist f3 - opd))
                      ltac:(apply OBR_fset_op; exact H3) ltac:(facc; lia) ltac:(facc; lia) Xwn ltac:(facc; lia) ltac:(facc; rewrite E3o', E3ob'; lia) ltac:(facc; lia))
            as (H4 & L4 & O4 & Ln4 & R4).
          revert L4 R4 O4. facc. intros L4 R4 O4.
          destruct (dist_tailcopy_rel x _ _ H4 Ln4 ltac:(lia) ltac:(rewrite L4; exact R4)) as (H5 & L5).
          split; [exact (OBRF_OBR _ _ H5)|]. split; [|rewrite L5, L4, E3ob'; exact HL].
          pose proof (dist_tailcopy_spec x (win_place x (fset_op f3 (f_dist f3 - opd))) Ln4) as (_ & _ & _ & _ & T5 & _). rewrite T5. lia.
      + cbn [RREL]. rewrite <- Eg3.
        destruct (out_copy_rel x f3 _ H3 ltac:(lia) ltac:(lia) ltac:(rewrite E3ob'; lia) ltac:(lia)) as (H5 & L5).
        split; [exact H5|]. split; [|rewrite L5, E3ob'; exact HL].
        pose proof (out_copy_spec x f3 ltac:(lia)) as (_ & _ & _ & _ & T5 & _). rewrite T5. lia.
    - rewrite Eg. obn. obs (fdrop f (code_bits here)) ob. rewrite <- fdrop_ob, <- Eg.
      destruct (Z.land (code_op here) 64 =? 0).
      + apply andb_prop in Hok as [B2 Hok]. apply andb_prop in Hok as [B3 Hok].
        apply IH; [exact Hd | facc; exact Hbeg | destruct f; exact HL | exact Hok].
      + cbn [RREL]. split; [exact Hd|]. split; [destruct f; cbn in *; lia|]. split; [destruct f; exact HL|]. split; reflexivity.
  Qed.
End B.

Lemma len_extra_ob : forall x e f ob, len_extra x e (fset_ob f ob) = fset_ob (len_extra x e f) ob.
Proof.
  intros x e f ob. unfold len_extra. obs f ob. rewrite !fpull_ob. obs (fpull x f) ob.
  destruct (negb (e =? 0)); [|reflexivity].
  destruct (f_bits f <? e); rewrite ?fset_len_ob, ?fdrop_ob; reflexivity.
Qed.
Lemma OBR_len_extra : forall x e f g, OBR f g -> OBR (len_extra x e f) (len_extra x e g) /\ f_out (len_extra x e f) = f_out f /\ f_ob (len_extra x e f) = f_ob f.
Proof.
  intros x e f g H. destruct (OBR_eq f g H) as [ob ->]. rewrite len_extra_ob. unfold len_extra.
  destruct (negb (e =? 0)); [|split; [exact H | split; reflexivity]].
  destruct (f_bits f <? e).
  - split; [rewrite <- fdrop_ob, <- fset_len_ob, <- fpull_ob; apply OBR_fdrop; apply OBR_fset_len; apply OBR_fpull; exact H | destruct f; split; reflexivity].
  - split; [rewrite <- fdrop_ob, <- fset_len_ob; apply OBR_fdrop; apply OBR_fset_len; exact H | destruct f; split; reflexivity].
Qed.

Lemma dolen_ok_S2 : forall x s IN ON WN k here f,
  dolen_ok x s IN ON WN (S k) here f =
    let op := code_bits here in
    (op <=? f_bits f) &&
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then f_out f <? ON
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      (if negb (op =? 0) then if f_bits f <? op then (f_in f + 1 <=? IN) && (op <=? f_bits f + 8) else true else true) &&
      let f := len_extra x op f in
      pull2_ok IN f &&
      let f := fpull2_if x f in
      let i := Z.land (f_hold f) (x_dmask x) in
      (i <? ctab_len (is_distcode s)) && dodist_ok x s IN ON WN 4 (code_at s (is_distcode s) i) f
    else if Z.land op 64 =? 0 then
      (op <? 16) &&
      let i := code_val here + Z.land (f_hold f) (zmask op) in
      (i <? ctab_len (is_lencode s)) && dolen_ok x s IN ON WN k (code_at s (is_lencode s) i) f
    else true.
Proof. intros. apply dolen_ok_S. Qed.

Lemma OBR_literal : forall f g v, OBR f g -> 0 <= f_out f < arr_len (f_ob f) ->
  OBR (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) v)) (f_out f + 1))
      (fset_out (fset_ob g (arr_set (f_ob g) (f_out g) v)) (f_out g + 1))
  /\ arr_len (f_ob (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) v)) (f_out f + 1))) = arr_len (f_ob f)
  /\ f_out (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) v)) (f_out f + 1)) = f_out f + 1.
Proof.
  intros f g v (ob & -> & [L E]) Ho. unfold OBR, obrel in *.
  destruct f as [fi fo fh fb fl fd fp fr fob]. facc. revert L E Ho. facc. intros L E Ho.
  split; [|split; [apply arr_len_set|reflexivity]].
  exists (arr_set ob fo v). split; [reflexivity|].
  split; [rewrite !arr_len_set; exact L|]. intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite L.
  destruct (Z.eqb_spec fo j) as [<-|NE]; cbn [andb].
  - rewrite (proj2 (Z.leb_le 0 fo)) by lia. rewrite (proj2 (Z.ltb_lt fo _)) by lia. reflexivity.
  - apply E. lia.
Qed.

Section B2.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

  Lemma dolen_relB : forall k here f g,
    OBR f g -> x_beg x <= f_out f -> arr_len (f_ob f) = ON ->
    dolen_ok x s IN ON WN k here f = true ->
    RREL ON (x_beg x) (dolen k x s here f) (dolen k x s here g).
  Proof.
    induction k as [|k IH]; intros here f g H Hbeg HL Hok; [discriminate Hok|].
    destruct (OBR_eq f g H) as [ob Eg].
    rewrite dolen_ok_S2 in Hok. rewrite !dolen_S. cbv zeta in Hok. cbv zeta.
    apply andb_prop in Hok as [B1 Hok].
    assert (Hd : OBR (fdrop f (code_bits here)) (fdrop g (code_bits here))) by (apply OBR_fdrop; exact H).
    rewrite Eg. obn. obs (fdrop f (code_bits here)) ob.
    assert (Edo : f_out (fdrop f (code_bits here)) = f_out f /\ f_ob (fdrop f (code_bits here)) = f_ob f) by (destruct f; split; reflexivity).
    destruct Edo as [Edo Edob].
    assert (Hd' : OBR (fdrop f (code_bits here)) (fset_ob (fdrop f (code_bits here)) ob)) by (rewrite <- fdrop_ob, <- Eg; exact Hd).
    destruct (code_op here =? 0).
    -
      apply Z.ltb_lt in Hok. cbn [RREL].
      destruct (OBR_literal _ _ (wrap8 (code_val here)) Hd' ltac:(rewrite Edo, Edob, HL; lia)) as (H5 & L5 & O5).
      rewrite f_ob_fset_ob in H5. obs (fdrop f (code_bits here)) ob.
      split; [exact H5|]. rewrite O5, L5, Edo, Edob. split; [lia | exact HL].
    - destruct (negb (Z.land (code_op here) 16 =? 0)).
      +
        apply andb_prop in Hok as [B2 Hok]. apply andb_prop in Hok as [B3 Hok]. apply andb_prop in Hok as [B4 Hok].
        set (e := Z.land (code_op here) 15) in *.
        rewrite len_extra_ob, fpull2_if_ob.
        destruct (OBR_len_extra x e (fset_len (fdrop f (code_bits here)) (code_val here)) (fset_ob (fset_len (fdrop f (code_bits here)) (code_val here)) ob)
                    ltac:(rewrite <- fset_len_ob; apply OBR_fset_len; exact Hd')) as (H2 & E2o & E2ob).
        set (f2 := len_extra x e (fset_len (fdrop f (code_bits here)) (code_val here))) in *.
        pose proof (OBR_fpull2_if x _ _ H2) as H3. rewrite len_extra_ob, fpull2_if_ob in H3.
        set (f3 := fpull2_if x f2) in *. obs f3 ob.
        assert (E3 : f_out f3 = f_out f /\ f_ob f3 = f_ob f).
        { subst f3. rewrite <- Edo, <- Edob.
          transitivity (f_out f2); [|rewrite E2o; reflexivity] || idtac.
          assert (X : f_out (fpull2_if x f2) = f_out f2 /\ f_ob (fpull2_if x f2) = f_ob f2) by (unfold fpull2_if; destruct (f_bits f2 <? 15); destruct f2; split; reflexivity).
          destruct X as [X1 X2]. rewrite X1, X2, E2o, E2ob. destruct f; split; reflexivity. }
        destruct E3 as [E3o E3ob].
        apply (dodist_relB x s IN ON WN Xbeg Xwn HON); [exact H3 | rewrite E3o; exact Hbeg | rewrite E3ob; exact HL | exact Hok].
      + destruct (Z.land (code_op here) 64 =? 0).
        * apply andb_prop in Hok as [B2 Hok]. apply andb_prop in Hok as [B3 Hok].
          apply IH; [exact Hd' | rewrite Edo; exact Hbeg | rewrite Edob; exact HL | exact Hok].
        * destruct (negb (Z.land (code_op here) 32 =? 0)); cbn [RREL]; (split; [exact Hd'|]); rewrite Edo, Edob; (split; [lia|]); (split; [exact HL|]); split; reflexivity.
  Qed.

  Lemma fast_trip_relB : forall f g,
    OBR f g -> x_beg x <= f_out f -> arr_len (f_ob f) = ON ->
    trip_ok x s IN ON WN f = true ->
    RREL ON (x_beg x) (fast_trip x s f) (fast_trip x s g).
  Proof.
    intros f g H Hbeg HL Hok. unfold fast_trip. unfold trip_ok in Hok. cbv zeta in Hok.
    apply andb_prop in Hok as [B1 Hok]. apply andb_prop in Hok as [B2 Hok].
    destruct (OBR_eq f g H) as [ob Eg]. rewrite Eg, fpull2_if_ob. obs (fpull2_if x f) ob. rewrite <- fpull2_if_ob, <- Eg.
    pose proof (OBR_fpull2_if x f g H) as H1.
    assert (E1 : f_out (fpull2_if x f) = f_out f /\ f_ob (fpull2_if x f) = f_ob f).
    { unfold fpull2_if. destruct (f_bits f <? 15); destruct f; split; reflexivity. }
    destruct E1 as [E1o E1ob].
    apply dolen_relB; [exact H1 | rewrite E1o; exact Hbeg | rewrite E1ob; exact HL | exact Hok].
  Qed.
End B2.


Section CheckerOb.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.

  Lemma window_ok_ob : forall f ob, window_ok x ON WN (fset_ob f ob) = window_ok x ON WN f.
  Proof. intros [] ob; reflexivity. Qed.
  Lemma pull2_ok_ob : forall f ob, pull2_ok IN (fset_ob f ob) = pull2_ok IN f.
  Proof. intros [] ob; reflexivity. Qed.
  Lemma exit_ok_ob : forall f ob, exit_ok (fset_ob f ob) = exit_ok f.
  Proof. intros [] ob; reflexivity. Qed.

  Lemma dodist_ok_ob : forall k here f ob, dodist_ok x s IN ON WN k here (fset_ob f ob) = dodist_ok x s IN ON WN k here f.
  Proof.
    induction k as [|k IH]; intros here f ob; [reflexivity|].
    rewrite !dodist_ok_S2. cbv zeta. obs f ob. obn. obs (fdrop f (code_bits here)) ob.
    obs (fset_dist (fdrop f (code_bits here)) (code_val here)) ob.
    rewrite dpulls_ob. obs (dpulls x (Z.land (code_op here) 15) (fset_dist (fdrop f (code_bits here)) (code_val here))) ob.
    rewrite dext_ob. obs (dext x (Z.land (code_op here) 15) (fset_dist (fdrop f (code_bits here)) (code_val here))) ob.
    rewrite fset_op_ob, window_ok_ob. rewrite IH. reflexivity.
  Qed.

  Lemma dolen_ok_ob : forall k here f ob, dolen_ok x s IN ON WN k here (fset_ob f ob) = dolen_ok x s IN ON WN k here f.
  Proof.
    induction k as [|k IH]; intros here f ob; [reflexivity|].
    rewrite !dolen_ok_S2. cbv zeta. obs f ob. obn. obs (fdrop f (code_bits here)) ob.
    obs (fset_len (fdrop f (code_bits here)) (code_val here)) ob.
    rewrite len_extra_ob, pull2_ok_ob, fpull2_if_ob.
    obs (fpull2_if x (len_extra x (Z.land (code_op here) 15) (fset_len (fdrop f (code_bits here)) (code_val here)))) ob.
    rewrite dodist_ok_ob, IH. reflexivity.
  Qed.

  Lemma trip_ok_ob : forall f ob, trip_ok x s IN ON WN (fset_ob f ob) = trip_ok x s IN ON WN f.
  Proof.
    intros f ob. unfold trip_ok. rewrite pull2_ok_ob, fpull2_if_ob. obs (fpull2_if x f) ob. rewrite dolen_ok_ob. reflexivity.
  Qed.
End CheckerOb.


Section Loop.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

  Let mstep := fun f => match fast_trip x s f with
                        | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', @None (Z * option Z))
                        | FBreak f' mode msg => inr (f', Some (mode, msg))
                        end.
  Let cstep := fun f => if trip_ok x s IN ON WN f then
                          match fast_trip x s f with
                          | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (exit_ok f')
                          | FBreak f' _ _ => inr (exit_ok f')
                          end
                        else inr false.

  Lemma loop_relB : forall n f g,
    OBR f g -> x_beg x <= f_out f -> arr_len (f_ob f) = ON ->
    iterZ (Z.of_nat n) cstep (fun _ => false) f = true ->
    let '(f1, m1) := iterZ (Z.of_nat n) mstep (fun f0 => (f0, None)) f in
    let '(g1, m2) := iterZ (Z.of_nat n) mstep (fun f0 => (f0, None)) g in
    OBR f1 g1 /\ m2 = m1 /\ arr_len (f_ob f1) = ON /\ iterZ (Z.of_nat n) cstep (fun _ => false) g = true.
  Proof.
    induction n as [|n IH]; intros f g H Hbeg HL HK.
    - cbn [Z.of_nat] in HK. rewrite iterZ_le0 in HK by lia. discriminate HK.
    - rewrite Nat2Z.inj_succ in HK |- *.
      rewrite iterZ_step in HK by lia. rewrite !iterZ_step by lia.
      replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) in HK |- * by lia.
      destruct (OBR_eq f g H) as [ob Eg].
      assert (TKg : trip_ok x s IN ON WN g = trip_ok x s IN ON WN f) by (rewrite Eg; apply trip_ok_ob).
      unfold cstep at 1 in HK. unfold cstep at 1. unfold mstep at 1 3. rewrite TKg.
      destruct (trip_ok x s IN ON WN f) eqn:TK; [|discriminate HK].
      pose proof (fast_trip_relB x s IN ON WN Xbeg Xwn HON f g H Hbeg HL TK) as R.
      destruct (fast_trip x s f) as [f'|f' md mg]; destruct (fast_trip x s g) as [g'|g' md' mg']; cbn [RREL] in R; try contradiction.
      + destruct R as (H' & Ho' & HL'). destruct (OBR_eq f' g' H') as [ob' Eg'].
        replace (f_in g') with (f_in f') by (rewrite Eg'; destruct f'; reflexivity).
        replace (f_out g') with (f_out f') by (rewrite Eg'; destruct f'; reflexivity).
        replace (exit_ok g') with (exit_ok f') by (rewrite Eg', exit_ok_ob; reflexivity).
        destruct ((f_in f' <? x_last x) && (f_out f' <? x_end x)).
        * apply IH; [exact H' | exact Ho' | exact HL' | exact HK].
        * repeat split; try assumption; try reflexivity.
      + destruct R as (H' & Ho' & HL' & -> & ->).
        replace (exit_ok g') with (exit_ok f') by (destruct (OBR_eq f' g' H') as [ob' ->]; rewrite exit_ok_ob; reflexivity).
        repeat split; try assumption; try reflexivity.
  Qed.
End Loop.


Definition ffloop (x : ffx) (s : inflate_state) (fuel : Z) (f0 : ffs) : ffs * option (Z * option Z) :=
  iterZ fuel
    (fun f => match fast_trip x s f with
              | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
              | FBreak f' mode msg => inr (f', Some (mode, msg))
              end)
    (fun f => (f, None)) f0.
Definition fffin (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).
Definition ffpost (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.
Lemma inflate_fast_eq' : forall s c r,
  inflate_fast (mkW s c r) = let '(f, mm) := ffloop (ffx_of s c r) s (8 * ic_avail_in c + ic_avail_out c + 80) (ff0_of s c) in
                             ffpost s c r (ffx_of s c r) (fffin f) mm.
Proof. intros. reflexivity. Qed.

Lemma fffin_ob : forall f ob, fffin (fset_ob f ob) = fset_ob (fffin f) ob.
Proof. intros [] ob; reflexivity. Qed.

Theorem inflate_fast_congr : forall (s : inflate_state) (c : icall) (r : iregs) (ob : arr),
    arr_len ob = arr_len (ic_outbuf c) ->
    (forall i, 0 <= i < ic_next_out c -> arr_get ob i = arr_get (ic_outbuf c) i) ->
    (forall i, 0 <= i < arr_len ob -> 0 <= arr_get ob i < 256) ->
    ff_ok s c r = true ->
    wrap32 (ir_out r - ic_avail_out c) <= ic_next_out c ->
    arr_len (ic_outbuf c) < 2 ^ 32 ->
    0 <= is_wnext s ->
    let w1 := inflate_fast (mkW s c r) in
    let w2 := inflate_fast (mkW s (icset_outbuf c ob) r) in
    ff_ok s (icset_outbuf c ob) r = true
    /\ w_s w2 = w_s w1 /\ w_r w2 = w_r w1
    /\ w_c w2 = icset_outbuf (w_c w1) (ic_outbuf (w_c w2))
    /\ arr_len (ic_outbuf (w_c w2)) = arr_len (ic_outbuf (w_c w1))
    /\ (forall i, 0 <= i < ic_next_out (w_c w1) -> arr_get (ic_outbuf (w_c w2)) i = arr_get (ic_outbuf (w_c w1)) i).
Proof.
  intros s c r ob HL HE HB HOK Hbeg HON Hwn. cbv zeta.
  rewrite !inflate_fast_eq'. unfold ff_ok in HOK |- *.
  assert (EX : ffx_of s (icset_outbuf c ob) r = ffx_of s c r) by (destruct c; reflexivity). rewrite !EX in *.
  assert (E0 : ff0_of s (icset_outbuf c ob) = fset_ob (ff0_of s c) ob) by (destruct c; reflexivity). rewrite !E0 in *.
  replace (ic_avail_in (icset_outbuf c ob)) with (ic_avail_in c) in * by (destruct c; reflexivity).
  replace (ic_avail_out (icset_outbuf c ob)) with (ic_avail_out c) in * by (destruct c; reflexivity).
  replace (arr_len (ic_outbuf (icset_outbuf c ob))) with (arr_len ob) by (destruct c; reflexivity). rewrite HL.
  replace (ic_input (icset_outbuf c ob)) with (ic_input c) by (destruct c; reflexivity).
  set (x := ffx_of s c r) in *. set (fuel := 8 * ic_avail_in c + ic_avail_out c + 80) in *.
  set (ON := arr_len (ic_outbuf c)) in *. set (IN := arr_len (ic_input c)) in *. set (WN := arr_len (is_window s)) in *.
  assert (Xbeg : 0 <= x_beg x <= f_out (ff0_of s c)).
  { subst x. unfold ffx_of, ff0_of. facc. pose proof (wrap32_range (ir_out r - ic_avail_out c)). lia. }
  assert (Xwn : 0 <= x_wnext x) by (subst x; unfold ffx_of; facc; exact Hwn).
  assert (H0 : OBR (ff0_of s c) (fset_ob (ff0_of s c) ob)).
  { exists ob. split; [reflexivity|]. unfold ff0_of. facc. split; [exact HL | intros i Hi; apply HE; exact Hi]. }
  assert (Hfuel : 0 <= fuel \/ fuel < 0) by lia.
  destruct (Z.lt_ge_cases fuel 0) as [NEG|POS].
  { unfold InffastSafe.loop_ok in HOK. rewrite iterZ_le0 in HOK by lia. discriminate HOK. }
  rewrite <- (Z2Nat.id fuel) in HOK |- * by lia.
  pose proof (loop_relB x s IN ON WN (proj1 Xbeg) Xwn HON (Z.to_nat fuel) (ff0_of s c) (fset_ob (ff0_of s c) ob) H0 (proj2 Xbeg)
                ltac:(unfold ff0_of; reflexivity) HOK) as LR.
  unfold ffloop. unfold InffastSafe.loop_ok.
  match type of LR with (let '(f1, m1) := ?A in let '(g1, m2) := ?B in _) => destruct A as [f1 m1]; destruct B as [g1 m2] end.
  destruct LR as (H1 & -> & HL1 & HOK2).
  split; [exact HOK2|].
  destruct (OBR_eq _ _ H1) as [ob1 Eg1]. rewrite Eg1, fffin_ob.
  destruct H1 as (ob1' & Eg1' & [L1 E1]). rewrite Eg1 in Eg1'. apply (f_equal f_ob) in Eg1'. rewrite !f_ob_fset_ob in Eg1'. subst ob1'.
  unfold ffpost. cbv zeta. obs (fffin f1) ob1.
  assert (Efo : f_out (fffin f1) = f_out f1) by (destruct f1; reflexivity).
  destruct m1 as [[md [mg|]]|]; cbn [w_s w_r w_c]; sacc; rewrite ?f_ob_fset_ob;
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [destruct c; reflexivity|]);
    (replace (f_ob (fffin f1)) with (f_ob f1) by (destruct f1; reflexivity)); rewrite Efo; (split; [exact L1 | exact E1]).
Qed.
