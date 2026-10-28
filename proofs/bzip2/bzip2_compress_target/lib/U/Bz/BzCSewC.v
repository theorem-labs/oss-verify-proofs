(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCSewB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zrange (lo hi : Z) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo))).

Lemma in_zrange : forall lo hi x, In x (zrange lo hi) <-> lo <= x < hi.
Proof.
  intros lo hi x. unfold zrange. rewrite in_map_iff. split.
  - cps_intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hx. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma zrange_NoDup : forall lo hi, NoDup (zrange lo hi).
Proof. intros. unfold zrange. apply NoDup_map_on; [apply seq_NoDup|]. intros a b _ _ H. lia. Qed.
Lemma zrange_length : forall lo hi, lo <= hi -> Z.of_nat (length (zrange lo hi)) = hi - lo.
Proof. intros. unfold zrange. rewrite length_map, length_seq. lia. Qed.

Lemma cntP_filter : forall P n, cntP P n = Z.of_nat (length (filter P (zrange 0 (Z.of_nat n)))).
Proof.
  intros P n. induction n as [|n IH]; [reflexivity|].
  cbn [cntP]. rewrite IH. unfold zrange.
  replace (Z.to_nat (Z.of_nat (S n) - 0)) with (S (Z.to_nat (Z.of_nat n - 0))) by lia.
  rewrite seq_S, map_app, filter_app, length_app. cbn [map filter Nat.add].
  replace (0 + Z.of_nat (Z.to_nat (Z.of_nat n - 0))) with (Z.of_nat n) by lia.
  destruct (P (Z.of_nat n)); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma NoDup_incl_Zlength : forall (l l' : list Z), NoDup l -> incl l l' -> Z.of_nat (length l) <= Z.of_nat (length l').
Proof. intros l l' ND INC. pose proof (NoDup_incl_length ND INC). lia. Qed.

Lemma NoDup_incl_both : forall (l l' : list Z), NoDup l -> NoDup l' -> incl l l' -> (length l' <= length l)%nat -> incl l' l.
Proof. intros l l' ND ND' INC LEN. apply NoDup_length_incl; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma clearmask_small : forall x, 0 <= x < 2097152 -> clearmask x = x.
Proof.
  intros x Hx. unfold clearmask.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 21) as [L|G].
  - replace (Z.testbit 4292870143 n) with true; [apply Bool.andb_true_r|].
    symmetry. assert (E : 4292870143 = Z.lor (Z.ones 21) (Z.shiftl 1023 22)) by reflexivity. rewrite E.
    rewrite Z.lor_spec, Z.ones_spec_low by lia. reflexivity.
  - replace (Z.testbit x n) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    assert (Z.log2 x < 21); [|lia]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    apply Z.log2_lt_pow2; [lia|]. change (2 ^ 21) with 2097152. lia.
Qed.

Lemma clearmask_marked : forall x, 0 <= x < 2097152 -> clearmask (Z.lor x SETMASK) = x.
Proof.
  intros x Hx. unfold clearmask, SETMASK.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n 21) as [->|NE].
  - replace (Z.testbit 4292870143 21) with false by reflexivity. rewrite Bool.andb_false_r.
    symmetry. apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    assert (Z.log2 x < 21); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 21) with 2097152. lia.
  - replace (Z.testbit 2097152 n) with false.
    2:{ symmetry. change 2097152 with (2 ^ 21). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
    rewrite Bool.orb_false_r.
    destruct (Z.lt_ge_cases n 21) as [L|G].
    + replace (Z.testbit 4292870143 n) with true; [apply Bool.andb_true_r|].
      symmetry. assert (E : 4292870143 = Z.lor (Z.ones 21) (Z.shiftl 1023 22)) by reflexivity. rewrite E.
      rewrite Z.lor_spec, Z.ones_spec_low by lia. reflexivity.
    + replace (Z.testbit x n) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
      assert (Z.log2 x < 21); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 21) with 2097152. lia.
Qed.

Lemma has_setmask_small : forall x, 0 <= x < 2097152 -> has_setmask x = false.
Proof.
  intros x Hx. unfold has_setmask, SETMASK. replace (Z.land x 2097152) with 0; [reflexivity|].
  symmetry. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 21) as [->|NE].
  - replace (Z.testbit x 21) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. assert (Z.log2 x < 21); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 21) with 2097152. lia.
  - change 2097152 with (2 ^ 21). rewrite Z.pow2_bits_eqb by lia. replace (21 =? n) with false by (symmetry; apply Z.eqb_neq; lia). apply Bool.andb_false_r.
Qed.

Lemma has_setmask_marked : forall x, 0 <= x -> has_setmask (Z.lor x SETMASK) = true.
Proof.
  intros x Hx. unfold has_setmask, SETMASK.
  destruct (Z.eqb_spec (Z.land (Z.lor x 2097152) 2097152) 0) as [E|NE]; [|reflexivity].
  exfalso. assert (T : Z.testbit (Z.land (Z.lor x 2097152) 2097152) 21 = true).
  { rewrite Z.land_spec, Z.lor_spec. change 2097152 with (2 ^ 21). rewrite Z.pow2_bits_true by lia. rewrite Bool.orb_true_r. reflexivity. }
  rewrite E, Z.bits_0 in T. discriminate.
Qed.

Lemma lor_setmask_idem : forall x, Z.lor (Z.lor x SETMASK) SETMASK = Z.lor x SETMASK.
Proof. intros. rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity. Qed.

Lemma lor_setmask_range : forall x, 0 <= x < 2097152 -> 0 <= Z.lor x SETMASK < 4294967296.
Proof.
  intros x Hx. unfold SETMASK. change 4294967296 with (2 ^ 32). apply lor_lt_pow2; change (2 ^ 32) with 4294967296; lia.
Qed.

(* [comment removed for export] *)
Definition ftcell (x c : Z) : Prop := x = c \/ x = Z.lor c SETMASK.
Lemma ftcell_clear : forall x c, 0 <= c < 2097152 -> ftcell x c -> clearmask x = c.
Proof. intros x c Hc [->| ->]; [apply clearmask_small| apply clearmask_marked]; exact Hc. Qed.
Lemma ftcell_mark : forall x c, ftcell x c -> ftcell (Z.lor x SETMASK) c.
Proof. intros x c [->| ->]; [right; reflexivity| right; apply lor_setmask_idem]. Qed.
Lemma ftcell_range : forall x c, 0 <= c < 2097152 -> ftcell x c -> 0 <= x < 4294967296.
Proof. intros x c Hc [->| ->]; [lia| apply lor_setmask_range; exact Hc]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Buckets.
  Variables (a2 : zarr) (nb : Z).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.

  Local Notation KEY := (key a2 nb).
  Local Notation NXT := (nxt nb).
  Local Notation CLM := (ClM a2 nb).
  Definition prv (u : Z) : Z := if u =? 0 then nb - 1 else u - 1.

  Lemma nxt_range : forall i, 0 <= i < nb -> 0 <= NXT i < nb.
  Proof. intros i Hi. unfold nxt, BzCPermM.nxt. destruct (Z.eqb_spec i (nb - 1)); lia. Qed.
  Lemma prv_range : forall u, 0 <= u < nb -> 0 <= prv u < nb.
  Proof. intros u Hu. unfold prv. destruct (Z.eqb_spec u 0); lia. Qed.
  Lemma nxt_prv : forall u, 0 <= u < nb -> NXT (prv u) = u.
  Proof. intros u Hu. unfold nxt, BzCPermM.nxt, prv. destruct (Z.eqb_spec u 0) as [->|N]; [rewrite Z.eqb_refl; reflexivity|].
    destruct (Z.eqb_spec (u - 1) (nb - 1)); lia. Qed.
  Lemma prv_nxt : forall i, 0 <= i < nb -> prv (NXT i) = i.
  Proof. intros i Hi. unfold nxt, BzCPermM.nxt, prv. destruct (Z.eqb_spec i (nb - 1)) as [->|N]; [rewrite Z.eqb_refl; reflexivity|].
    destruct (Z.eqb_spec (i + 1) 0); lia. Qed.
  Lemma nxt_inj : forall i j, 0 <= i < nb -> 0 <= j < nb -> NXT i = NXT j -> i = j.
  Proof. intros i j Hi Hj E. rewrite <- (prv_nxt i Hi), <- (prv_nxt j Hj), E. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma prv_model : forall u, 0 <= u < nb -> (let k := u - 1 in if k <? 0 then k + nb else k) = prv u.
  Proof. intros u Hu. cbv zeta. unfold prv. destruct (Z.ltb_spec (u - 1) 0), (Z.eqb_spec u 0); lia. Qed.

  Lemma key_split : forall i, KEY i = 256 * rd8 a2 i + rd8 a2 (NXT i).
  Proof. reflexivity. Qed.
  Lemma key_chars : forall i c c', 0 <= c' < 256 -> (KEY i = 256 * c + c' <-> rd8 a2 i = c /\ rd8 a2 (NXT i) = c').
  Proof. intros i c c' Hc'. rewrite key_split. pose proof (BB i). pose proof (BB (NXT i)). split; [intros E| intros [-> ->]; reflexivity]. split; lia. Qed.

  (* [comment removed for export] *)
  Definition Kset (v : Z) : list Z := filter (fun i => KEY i =? v) (zrange 0 nb).
  Lemma in_Kset : forall v i, In i (Kset v) <-> 0 <= i < nb /\ KEY i = v.
  Proof. intros v i. unfold Kset. rewrite filter_In, in_zrange. rewrite Z.eqb_eq. tauto. Qed.
  Lemma Kset_NoDup : forall v, NoDup (Kset v). Proof. intros. unfold Kset. apply NoDup_filter. apply zrange_NoDup. Qed.
  Lemma Kset_size : forall v, Z.of_nat (length (Kset v)) = CLM (v + 1) - CLM v.
  Proof.
    intros v. rewrite (ClM_step a2 nb ltac:(lia)). unfold EqM. rewrite cntP_filter.
    replace (Z.of_nat (Z.to_nat nb)) with nb by lia. unfold Kset. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma R_disjoint : forall v w p, v <> w -> CLM v <= p < CLM (v + 1) -> ~ (CLM w <= p < CLM (w + 1)).
  Proof.
    intros v w p NE Hp Hq. destruct (Z.lt_ge_cases v w) as [L|G].
    - pose proof (ClM_mono a2 nb (v + 1) w ltac:(lia)). lia.
    - pose proof (ClM_mono a2 nb (w + 1) v ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bucket_of : forall p, 0 <= p < nb -> exists v, 0 <= v < 65536 /\ CLM v <= p < CLM (v + 1).
  Proof.
    intros p Hp.
    assert (G : forall n : nat, (n <= 65536)%nat -> p < CLM (Z.of_nat n) -> exists v, 0 <= v < Z.of_nat n /\ CLM v <= p < CLM (v + 1)).
    { induction n as [|n IH]; intros Hn Hlt.
      - change (Z.of_nat 0) with 0 in Hlt. rewrite (ClM_0 a2 nb BB) in Hlt. lia.
      - destruct (Z.lt_ge_cases p (CLM (Z.of_nat n))) as [L|Ge].
        + cps_destruct (IH ltac:(lia) L) as (v & Hv & R). exists v. split; [lia| exact R].
        + exists (Z.of_nat n). split; [lia|]. replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia. lia. }
    cps_destruct (G 65536%nat ltac:(lia)) as (v & Hv & R).
    { change (Z.of_nat 65536) with 65536. rewrite (ClM_top a2 nb BB ltac:(lia)); lia. }
    exists v. split; [| exact R]. change (Z.of_nat 65536) with 65536 in Hv. lia.
  Qed.

  Lemma R_range : forall v p, CLM v <= p < CLM (v + 1) -> 0 <= p < nb.
  Proof. intros v p Hp. pose proof (ClM_range a2 nb ltac:(lia) v). pose proof (ClM_range a2 nb ltac:(lia) (v + 1)). lia. Qed.

  (* [comment removed for export] *)
  Definition BEX (a : zarr) (v : Z) : Prop :=
    (forall p, CLM v <= p < CLM (v + 1) -> 0 <= rd32 a p < nb /\ KEY (rd32 a p) = v) /\
    (forall p q, CLM v <= p < CLM (v + 1) -> CLM v <= q < CLM (v + 1) -> rd32 a p = rd32 a q -> p = q).

  (* [comment removed for export] *)
  Lemma BEX_cover : forall a v, BEX a v -> forall i, 0 <= i < nb -> KEY i = v -> exists p, CLM v <= p < CLM (v + 1) /\ rd32 a p = i.
  Proof.
    intros a v [V INJ] i Hi Ki.
    set (L := map (fun p => rd32 a p) (zrange (CLM v) (CLM (v + 1)))).
    assert (ND : NoDup L).
    { subst L. apply NoDup_map_on; [apply zrange_NoDup|]. intros p q Hp Hq E. apply in_zrange in Hp. apply in_zrange in Hq. apply INJ; assumption. }
    assert (INC : incl L (Kset v)).
    { intros x Hx. subst L. apply in_map_iff in Hx. cps_destruct Hx as (p & <- & Hp). apply in_zrange in Hp. apply in_Kset. apply V. exact Hp. }
    assert (LEN : (length (Kset v) <= length L)%nat).
    { pose proof (Kset_size v). subst L. rewrite length_map. pose proof (zrange_length (CLM v) (CLM (v + 1)) (ClM_mono a2 nb v (v + 1) ltac:(lia))). lia. }
    pose proof (NoDup_incl_both L (Kset v) ND (Kset_NoDup v) INC LEN) as BACK.
    pose proof (BACK i ltac:(apply in_Kset; split; assumption)) as IN.
    subst L. apply in_map_iff in IN. cps_destruct IN as (p & E & Hp). apply in_zrange in Hp. exists p. split; [exact Hp| exact E].
  Qed.

  Lemma BEX_ext : forall a a' v, BEX a v -> (forall p, CLM v <= p < CLM (v + 1) -> rd32 a' p = rd32 a p) -> BEX a' v.
  Proof.
    intros a a' v [V INJ] E. split.
    - intros p Hp. rewrite E by exact Hp. apply V. exact Hp.
    - intros p q Hp Hq H. rewrite !E in H by assumption. apply INJ; assumption.
  Qed.

  Definition PINV (a : zarr) : Prop := forall v, 0 <= v < 65536 -> BEX a v.

  Lemma PINV_perm : forall a, PINV a -> fm_perm a nb.
  Proof.
    intros a P. split.
    - intros x Hx. cps_destruct (bucket_of x Hx) as (v & Hv & R). apply (proj1 (P v Hv)). exact R.
    - intros x y Hx Hy E. cps_destruct (bucket_of x Hx) as (v & Hv & Rx). cps_destruct (bucket_of y Hy) as (w & Hw & Ry).
      pose proof (proj2 (proj1 (P v Hv) x Rx)) as Kx. pose proof (proj2 (proj1 (P w Hw) y Ry)) as Ky.
      rewrite E in Kx. assert (Hvw : v = w) by congruence. rewrite <- Hvw in Ry. apply (proj2 (P v Hv)); [exact Rx | exact Ry | exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma PINV_perm_frame : forall a a' v, PINV a -> 0 <= v < 65536 -> fm_perm a' nb ->
    frame_out a a' (CLM v) (CLM (v + 1) - 1) -> PINV a'.
  Proof.
    intros a a' v P Hv PM FR w Hw.
    destruct (Z.eq_dec w v) as [->|NE].
    - split.
      + intros p Hp. pose proof (R_range v p Hp) as Pp. pose proof (proj1 PM p Pp) as RG. split; [exact RG|].
        pose proof (key_range a2 nb BB (rd32 a' p)) as KR.
        destruct (Z.eq_dec (KEY (rd32 a' p)) v) as [E|NK]; [exact E|]. exfalso.
        cps_destruct (BEX_cover a (KEY (rd32 a' p)) (P (KEY (rd32 a' p)) KR) (rd32 a' p) RG eq_refl) as (q & Hq & Eq).
        assert (NQ : ~ (CLM v <= q < CLM (v + 1))) by (apply (R_disjoint (KEY (rd32 a' p))); [exact NK| exact Hq]).
        rewrite <- (FR q) in Eq by lia.
        pose proof (proj2 PM p q Pp (R_range _ q Hq) (eq_sym Eq)). subst q. exact (NQ Hp).
      + intros p q Hp Hq E. apply (proj2 PM); [eapply R_range; eassumption| eapply R_range; eassumption| exact E].
    - apply (BEX_ext a a' w (P w Hw)). intros p Hp. apply FR.
      pose proof (R_disjoint w v p NE Hp). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PINV_of_KpM : forall r, (forall i, 0 <= i < nb -> rd32 r (KpM a2 nb i) = i) -> PINV r.
  Proof.
    intros r HR v Hv. split.
    - intros p Hp. pose proof (R_range v p Hp) as Pp.
      cps_destruct (KpM_onto a2 nb ltac:(lia) p Pp) as (i & Hi & <-). rewrite HR by exact Hi. split; [exact Hi|].
      pose proof (KpM_bucket a2 nb ltac:(lia) i Hi) as KB.
      destruct (Z.eq_dec (KEY i) v) as [E|NE]; [exact E|]. exfalso. exact (R_disjoint (KEY i) v (KpM a2 nb i) NE KB Hp).
    - intros p q Hp Hq E.
      cps_destruct (KpM_onto a2 nb ltac:(lia) p (R_range v p Hp)) as (i & Hi & <-).
      cps_destruct (KpM_onto a2 nb ltac:(lia) q (R_range v q Hq)) as (i' & Hi' & <-).
      rewrite !HR in E by assumption. subst i'. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Side.
    Variable ss : Z.
    Hypothesis SS : 0 <= ss < 256.
    Let B := fun i => rd8 a2 i.

    Fixpoint side (f : nat) (u : Z) : option bool :=
      match f with
      | O => None
      | S f' => if B (NXT u) =? ss then side f' (NXT u) else Some (B (NXT u) <? ss)
      end.
    Definition SIDE (u : Z) : option bool := side (Z.to_nat nb) u.
    (* [comment removed for export] *)
    Definition NALL : Prop := exists z, 0 <= z < nb /\ B z <> ss.

    Lemma side_more : forall f g u b, side f u = Some b -> side (f + g) u = Some b.
    Proof.
      induction f as [|f IH]; intros g u b H; cbn [side Nat.add] in *; [discriminate|].
      destruct (B (NXT u) =? ss); [apply IH; exact H| exact H].
    Qed.

    Lemma mod_step : forall z u, 0 <= u < nb -> 0 <= z < nb -> z <> u -> (z - NXT u) mod nb = (z - u) mod nb - 1.
    Proof.
      intros z u Hu Hz NE. unfold nxt, BzCPermM.nxt.
      assert (M1 : 1 <= (z - u) mod nb).
      { destruct (Z.lt_ge_cases z u) as [L|G].
        - replace ((z - u) mod nb) with (z - u + nb); [lia|]. symmetry. rewrite <- (Z_mod_plus_full (z - u) 1 nb). replace (z - u + 1 * nb) with (z - u + nb) by lia. rewrite Z.mod_small; lia.
        - rewrite Z.mod_small; lia. }
      destruct (Z.eqb_spec u (nb - 1)) as [->|N].
      - replace (z - 0) with z by lia. rewrite (Z.mod_small z nb) by lia.
        replace (z - (nb - 1)) with (z + 1 + (-1) * nb) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
      - destruct (Z.lt_ge_cases z u) as [L|G].
        + replace (z - (u + 1)) with ((z - u - 1 + nb) + (-1) * nb) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (z - u - 1 + nb)) by lia.
          replace (z - u) with ((z - u + nb) + (-1) * nb) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
        + rewrite !Z.mod_small; lia.
    Qed.

    Lemma side_some : forall z, 0 <= z < nb -> B z <> ss ->
      forall f u, 0 <= u < nb -> z <> u -> (Z.to_nat ((z - u) mod nb) <= f)%nat -> side f u <> None.
    Proof.
      intros z Hz Bz. induction f as [|f IH]; intros u Hu NE Hf.
      - exfalso. pose proof (Z.mod_pos_bound (z - u) nb ltac:(lia)).
        assert ((z - u) mod nb = 0) by lia.
        apply NE. destruct (Z.lt_ge_cases z u) as [L|G].
        + replace (z - u) with ((z - u + nb) + (-1) * nb) in H0 by lia. rewrite Z_mod_plus_full, Z.mod_small in H0; lia.
        + rewrite Z.mod_small in H0; lia.
      - cbn [side]. destruct (Z.eqb_spec (B (NXT u)) ss) as [E|N]; [|discriminate].
        assert (NZ : NXT u <> z) by (intros X; rewrite X in E; exact (Bz E)).
        apply IH; [apply nxt_range; exact Hu| congruence|]. rewrite mod_step by (try lia; congruence). lia.
    Qed.

    Lemma SIDE_some : NALL -> forall u, 0 <= u < nb -> B u = ss -> SIDE u <> None.
    Proof.
      (cps_intros (z & Hz & Bz); intros u Hu Bu). unfold SIDE. apply (side_some z Hz Bz); [exact Hu| congruence|].
      pose proof (Z.mod_pos_bound (z - u) nb ltac:(lia)). lia.
    Qed.

    Lemma SIDE_seed : forall u, B (NXT u) <> ss -> SIDE u = Some (B (NXT u) <? ss).
    Proof.
      intros u H. unfold SIDE. destruct (Z.to_nat nb) as [|n] eqn:E; [lia|]. cbn [side].
      destruct (Z.eqb_spec (B (NXT u)) ss); [congruence| reflexivity].
    Qed.

    Lemma side_S : forall f u, side (S f) u = (if B (NXT u) =? ss then side f (NXT u) else Some (B (NXT u) <? ss)).
    Proof. reflexivity. Qed.

    Lemma SIDE_nxt : NALL -> forall k, 0 <= k < nb -> B (NXT k) = ss -> SIDE k = SIDE (NXT k).
    Proof.
      intros NA k Hk Bk. cps_pose NA as (z & Hz & Bz). unfold SIDE. destruct (Z.to_nat nb) as [|n] eqn:E; [lia|].
      rewrite (side_S n k). rewrite Bk, Z.eqb_refl.
      assert (SN : side n (NXT k) <> None).
      { apply (side_some z Hz Bz); [apply nxt_range; exact Hk| intros X; rewrite X in Bz; congruence|].
        pose proof (Z.mod_pos_bound (z - NXT k) nb ltac:(lia)). lia. }
      destruct (side n (NXT k)) as [b|] eqn:SB; [|congruence].
      symmetry. pose proof (side_more n 1 (NXT k) b SB) as SM. rewrite Nat.add_1_r in SM. exact SM.
    Qed.
  End Side.
End Buckets.
End BzCSewB.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB.
Import ListNotations.

Module BzCSewG.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition zperm (a : zarr) (n : Z) : Prop :=
  (forall i, 0 <= i < n -> 0 <= zget a i < n) /\
  (forall i j, 0 <= i < n -> 0 <= j < n -> zget a i = zget a j -> i = j).

Definition zswap (a : zarr) (x y : Z) : zarr := zset (zset a x (zget a y)) y (zget a x).

Lemma zswap_get : forall a x y k, zget (zswap a x y) k = (if k =? y then zget a x else if k =? x then zget a y else zget a k).
Proof. intros. unfold zswap. rewrite !zget_zset. destruct (Z.eqb_spec k y), (Z.eqb_spec k x); try reflexivity. Qed.

Lemma zperm_ext : forall a a' n, zperm a n -> (forall i, 0 <= i < n -> zget a' i = zget a i) -> zperm a' n.
Proof.
  intros a a' n [R I] E. split.
  - intros i Hi. rewrite E by exact Hi. apply R. exact Hi.
  - intros i j Hi Hj H. rewrite !E in H by assumption. apply I; assumption.
Qed.

Lemma zperm_swap : forall a n x y, zperm a n -> 0 <= x < n -> 0 <= y < n -> zperm (zswap a x y) n.
Proof.
  intros a n x y [R I] Hx Hy. split.
  - intros i Hi. rewrite zswap_get. destruct (Z.eqb_spec i y); [apply R; lia|]. destruct (Z.eqb_spec i x); [apply R; lia|]. apply R; lia.
  - intros i j Hi Hj H. rewrite !zswap_get in H.
    destruct (Z.eqb_spec i y), (Z.eqb_spec i x), (Z.eqb_spec j y), (Z.eqb_spec j x); subst;
      try reflexivity; try (pose proof (I _ _ Hx Hy H)); try (pose proof (I _ _ Hy Hx H)); try lia;
      first [ pose proof (I x j Hx Hj H); lia | pose proof (I y j Hy Hj H); lia | pose proof (I i x Hi Hx H); lia | pose proof (I i y Hi Hy H); lia | pose proof (I i j Hi Hj H); lia ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_ro_init_spec : forall n bd ro i0,
  let r := ms_ro_init n bd ro i0 in
  (forall i, i0 <= i < i0 + Z.of_nat n -> zget (fst r) i = 0 /\ zget (snd r) i = i) /\
  (forall i, (i < i0 \/ i0 + Z.of_nat n <= i) -> zget (fst r) i = zget bd i /\ zget (snd r) i = zget ro i).
Proof.
  induction n as [|n IH]; intros bd ro i0; cbv zeta; cbn [ms_ro_init].
  - cbn [fst snd]. split; [intros; lia| intros; split; reflexivity].
  - destruct (IH (zset bd i0 0) (zset ro i0 i0) (i0 + 1)) as [V F]. split.
    + intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
      * destruct (F i0 ltac:(lia)) as [F1 F2]. rewrite F1, F2, !zget_zset_same. split; reflexivity.
      * apply V. lia.
    + intros i Hi. destruct (F i ltac:(lia)) as [F1 F2]. rewrite F1, F2, !zget_zset_other by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_sh_shift_S : forall f ro ft h j vv,
  ms_sh_shift (S f) ro ft h j vv =
  (if bigfreq ft vv <? bigfreq ft (zget ro (j - h)) then
     let ro' := zset ro j (zget ro (j - h)) in let j' := j - h in
     if j' <=? h - 1 then (ro', j') else ms_sh_shift f ro' ft h j' vv
   else (ro, j)).
Proof. reflexivity. Qed.

Section Shell.
  Let N := 256.

  (* [comment removed for export] *)
  Lemma sh_shift_hole : forall f ro ft h j vv,
    1 <= h -> h <= j < N -> 0 <= vv < N -> zperm (zset ro j vv) N ->
    let r := ms_sh_shift f ro ft h j vv in
    0 <= snd r < N /\ zperm (zset (fst r) (snd r) vv) N.
  Proof.
    induction f as [|f IH]; intros ro ft h j vv Hh Hj Hv P; cbv zeta.
    - cbn [ms_sh_shift fst snd]. split; [lia| exact P].
    - rewrite ms_sh_shift_S. destruct (bigfreq ft vv <? bigfreq ft (zget ro (j - h))).
      + cbv zeta.
        assert (P' : zperm (zset (zset ro j (zget ro (j - h))) (j - h) vv) N).
        { apply (zperm_ext (zswap (zset ro j vv) j (j - h)) _ N).
          - apply zperm_swap; [exact P| lia| lia].
          - intros i Hi. rewrite zswap_get, !zget_zset.
            destruct (Z.eqb_spec i (j - h)), (Z.eqb_spec i j), (Z.eqb_spec (j - h) j), (Z.eqb_spec j j); try lia; reflexivity. }
        destruct (Z.leb_spec (j - h) (h - 1)) as [ST|GO].
        * cbn [fst snd]. split; [lia| exact P'].
        * apply IH; try assumption; lia.
      + cbn [fst snd]. split; [lia| exact P].
  Qed.

  Lemma sh_pass_perm : forall n ro ft h i, 1 <= h -> h <= i -> i + Z.of_nat n <= N -> zperm ro N -> zperm (ms_sh_pass n ro ft h i) N.
  Proof.
    induction n as [|n IH]; intros ro ft h i Hh Hi Hn P; cbn [ms_sh_pass]; [exact P|].
    pose proof (sh_shift_hole 300 ro ft h i (zget ro i) Hh ltac:(lia) ltac:(apply (proj1 P); lia)) as SH.
    cbv zeta in SH. destruct (ms_sh_shift 300 ro ft h i (zget ro i)) as [ro' j]. cbn [fst snd] in *.
    destruct SH as [Hj P'].
    { apply (zperm_ext ro); [exact P|]. intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k i) as [->|]; reflexivity. }
    apply IH; try lia. exact P'.
  Qed.

  Lemma ms_shell_S : forall f ro ft h,
    ms_shell (S f) ro ft h = (let h' := h / 3 in let ro' := ms_sh_pass (Z.to_nat (256 - h')) ro ft h' h' in if h' =? 1 then ro' else ms_shell f ro' ft h').
  Proof. reflexivity. Qed.

  Lemma pass_perm' : forall ro ft h, 1 <= h <= 256 -> zperm ro N -> zperm (ms_sh_pass (Z.to_nat (256 - h)) ro ft h h) N.
  Proof. intros ro ft h Hh P. apply sh_pass_perm; try lia. exact P. Qed.

  (* [comment removed for export] *)
  Lemma shell364_perm : forall ro ft, zperm ro N -> zperm (ms_shell 8 ro ft 364) N.
  Proof.
    intros ro ft P.
    rewrite ms_shell_S. cbv zeta. change (364 / 3) with 121. cbn [Z.eqb Pos.eqb].
    rewrite ms_shell_S. cbv zeta. change (121 / 3) with 40. cbn [Z.eqb Pos.eqb].
    rewrite ms_shell_S. cbv zeta. change (40 / 3) with 13. cbn [Z.eqb Pos.eqb].
    rewrite ms_shell_S. cbv zeta. change (13 / 3) with 4. cbn [Z.eqb Pos.eqb].
    rewrite ms_shell_S. cbv zeta. change (4 / 3) with 1. cbn [Z.eqb Pos.eqb].
    repeat (apply pass_perm'; [lia|]). exact P.
  Qed.
End Shell.

(* [comment removed for export] *)
Theorem runningOrder_perm : forall bd0 ro0 ft,
  let '(bd, ro) := ms_ro_init 256 bd0 ro0 0 in
  let ro' := ms_shell 8 ro ft 364 in
  (forall c, 0 <= c < 256 -> zget bd c = 0) /\
  (forall i, 0 <= i < 256 -> 0 <= zget ro' i < 256) /\
  (forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget ro' i = zget ro' i' -> i = i').
Proof.
  intros bd0 ro0 ft.
  pose proof (ms_ro_init_spec 256 bd0 ro0 0) as RI. cbv zeta in RI.
  destruct (ms_ro_init 256 bd0 ro0 0) as [bd ro]. cbn [fst snd] in RI. destruct RI as [V _].
  change (0 + Z.of_nat 256) with 256 in V. cbv zeta.
  assert (P : zperm ro 256).
  { split; [intros i Hi; rewrite (proj2 (V i Hi)); lia|]. intros i j Hi Hj E. rewrite (proj2 (V i Hi)), (proj2 (V j Hj)) in E. exact E. }
  pose proof (shell364_perm ro ft P) as [R I].
  split; [intros c Hc; apply (proj1 (V c Hc))|]. split; [exact R| exact I].
Qed.
End BzCSewG.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma ms_copy_fwd_S : forall f a1 cs a2 bd nblock ss j,
  ms_copy_fwd (S f) a1 cs a2 bd nblock ss j =
  (if j <? zget cs ss then
     let k := rd32 a1 j - 1 in let k := if k <? 0 then k + nblock else k in
     let c1 := rd8 a2 k in
     let '(a1, cs) := (if zget bd c1 =? 0 then (wr32 a1 (zget cs c1) k, zset cs c1 (zget cs c1 + 1)) else (a1, cs)) in
     ms_copy_fwd f a1 cs a2 bd nblock ss (j + 1)
   else (a1, cs, j)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma region_le : forall (a : zarr) lo hi (L : list Z),
  NoDup L -> lo <= hi ->
  (forall q, lo <= q < hi -> In (rd32 a q) L) ->
  (forall q q', lo <= q < hi -> lo <= q' < hi -> rd32 a q = rd32 a q' -> q = q') ->
  hi - lo <= Z.of_nat (length L).
Proof.
  intros a lo hi L ND LE IN INJ.
  pose proof (NoDup_incl_Zlength (map (fun q => rd32 a q) (zrange lo hi)) L) as H.
  rewrite length_map, zrange_length in H by exact LE. apply H.
  - apply NoDup_map_on; [apply zrange_NoDup|]. intros p q Hp Hq E. apply in_zrange in Hp. apply in_zrange in Hq. apply INJ; assumption.
  - intros x Hx. apply in_map_iff in Hx. cps_destruct Hx as (q & <- & Hq). apply in_zrange in Hq. apply IN. exact Hq.
Qed.

Lemma region_eq : forall (a : zarr) lo hi (L : list Z),
  NoDup L -> lo <= hi ->
  (forall q, lo <= q < hi -> In (rd32 a q) L) ->
  (forall q q', lo <= q < hi -> lo <= q' < hi -> rd32 a q = rd32 a q' -> q = q') ->
  (forall x, In x L -> exists q, lo <= q < hi /\ rd32 a q = x) ->
  hi - lo = Z.of_nat (length L).
Proof.
  intros a lo hi L ND LE IN INJ COV.
  pose proof (region_le a lo hi L ND LE IN INJ) as H1.
  pose proof (NoDup_incl_Zlength L (map (fun q => rd32 a q) (zrange lo hi)) ND) as H2.
  rewrite length_map, zrange_length in H2 by exact LE.
  assert (Z.of_nat (length L) <= hi - lo); [|lia]. apply H2.
  intros x Hx. cps_destruct (COV x Hx) as (q & Hq & <-). apply in_map_iff. exists q. split; [reflexivity|]. apply in_zrange. exact Hq.
Qed.

Lemma NoDup_remove_dec : forall (l : list Z) (x : Z), NoDup l -> NoDup (remove Z.eq_dec x l).
Proof.
  intros l x ND. induction ND as [|y l Hy ND IH]; cbn; [constructor|].
  destruct (Z.eq_dec x y); [exact IH|]. constructor; [| exact IH].
  intros Hin. apply in_remove in Hin. destruct Hin as [Hin _]. exact (Hy Hin).
Qed.

Lemma region_lt : forall (a : zarr) lo hi (L : list Z) (x : Z),
  NoDup L -> lo <= hi -> In x L ->
  (forall q, lo <= q < hi -> In (rd32 a q) L /\ rd32 a q <> x) ->
  (forall q q', lo <= q < hi -> lo <= q' < hi -> rd32 a q = rd32 a q' -> q = q') ->
  hi - lo + 1 <= Z.of_nat (length L).
Proof.
  intros a lo hi L x ND LE IN H INJ.
  pose proof (region_le a lo hi (remove Z.eq_dec x L) (NoDup_remove_dec L x ND) LE) as RL.
  pose proof (remove_length_lt Z.eq_dec L x IN) as LT.
  assert (hi - lo <= Z.of_nat (length (remove Z.eq_dec x L))); [|lia].
  apply RL; [|exact INJ]. intros q Hq. destruct (H q Hq) as [A B]. apply in_in_remove; [congruence| exact A].
Qed.

Section Copy.
  Variables (a2 : zarr) (nb ss : Z) (bd P0 : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis SS : 0 <= ss < 256.
  Hypothesis BD : zget bd ss = 0.
  Hypothesis P0X : PINV a2 nb P0.
  Hypothesis NA : NALL a2 nb ss.
  (* [comment removed for export] *)
  Variable a2r : zarr.
  Hypothesis AGR : forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k.

  Local Notation KEY := (key a2 nb).
  Local Notation NXT := (nxt nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation PRV := (prv nb).
  Local Notation SD := (SIDE a2 nb ss).

  Definition cs0 (c : Z) : Z := CLM (256 * c + ss).
  Definition ce1 (c : Z) : Z := CLM (256 * c + ss + 1).
  Definition B0 : Z := CLM (256 * ss).
  Definition B1 : Z := CLM (256 * (ss + 1)).

  (* [comment removed for export] *)
  Definition sideb (b : bool) (k : Z) : bool := match SD k with Some b' => Bool.eqb b b' | None => false end.
  Definition Fset (c : Z) (b : bool) : list Z := filter (sideb b) (Kset a2 nb (256 * c + ss)).

  Lemma in_Fset : forall c b k, In k (Fset c b) <-> 0 <= k < nb /\ KEY k = 256 * c + ss /\ SD k = Some b.
  Proof.
    intros c b k. unfold Fset. rewrite filter_In, (in_Kset a2 nb NB).
    assert (E : sideb b k = true <-> SD k = Some b).
    { unfold sideb. destruct (SD k) as [b'|]; [| split; intros; discriminate].
      destruct b, b'; cbn; split; intros; congruence. }
    rewrite E. all: tauto.
  Qed.
  Lemma Fset_NoDup : forall c b, NoDup (Fset c b).
  Proof. intros. unfold Fset. apply NoDup_filter. apply Kset_NoDup. Qed.

  (* [comment removed for export] *)
  Lemma filter_split_eq : forall (P Q : Z -> bool) (l : list Z), (forall x, P x = true -> Q x = true -> False) ->
    (forall x, In x l -> P x = true \/ Q x = true) ->
    (length (filter P l) + length (filter Q l) = length l)%nat.
  Proof.
    intros P Q l H C. induction l as [|x l IH]; cbn; [lia|].
    assert (IH' := IH ltac:(intros y Hy; apply C; right; exact Hy)).
    destruct (C x ltac:(left; reflexivity)) as [E|E]; rewrite E; destruct (P x) eqn:EP, (Q x) eqn:EQ; cbn; try lia; try congruence.
    all: exfalso; exact (H x EP EQ).
  Qed.

  Lemma Fset_sum : forall c, 0 <= c < 256 ->
    Z.of_nat (length (Fset c true)) + Z.of_nat (length (Fset c false)) = ce1 c - cs0 c.
  Proof.
    intros c Hc. unfold Fset, ce1, cs0. rewrite <- (Kset_size a2 nb NB).
    rewrite <- Nat2Z.inj_add. apply Nat2Z.inj_iff. apply filter_split_eq.
    - intros x P Q. unfold sideb in *. destruct (SD x) as [[|]|]; cbn in *; discriminate.
    - intros x Hx. apply (in_Kset a2 nb NB) in Hx. destruct Hx as [Rx Kx].
      destruct (proj1 (key_chars a2 nb BB x c ss SS) Kx) as [_ Bn].
      pose proof (SIDE_nxt a2 nb NB ss NA x Rx Bn) as SN.
      pose proof (SIDE_some a2 nb NB ss NA (NXT x) (nxt_range nb NB x Rx) Bn) as SM.
      unfold sideb. rewrite SN. destruct (SD (NXT x)) as [[|]|]; cbn; [left| right|]; try reflexivity. exfalso. exact (SM eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs0_le_ce1 : forall c, cs0 c <= ce1 c.
  Proof. intros. unfold cs0, ce1. apply ClM_mono. lia. Qed.
  Lemma ce1_le_nb : forall c, ce1 c <= nb.
  Proof. intros. unfold ce1. apply (ClM_range a2 nb ltac:(lia)). Qed.
  Lemma cs0_ge_0 : forall c, 0 <= cs0 c.
  Proof. intros. unfold cs0. apply (ClM_range a2 nb ltac:(lia)). Qed.
  Lemma B0_le_S0 : B0 <= cs0 ss.
  Proof. unfold B0, cs0. apply ClM_mono. lia. Qed.
  Lemma S1_le_B1 : ce1 ss <= B1.
  Proof. unfold ce1, B1. apply ClM_mono. lia. Qed.
  Lemma B0_ge_0 : 0 <= B0. Proof. unfold B0. apply (ClM_range a2 nb ltac:(lia)). Qed.
  Lemma B1_le_nb : B1 <= nb. Proof. unfold B1. apply (ClM_range a2 nb ltac:(lia)). Qed.

  (* [comment removed for export] *)
  Lemma seed_bucket : forall p, B0 <= p < cs0 ss -> exists c, 0 <= c < ss /\ CLM (256 * ss + c) <= p < CLM (256 * ss + c + 1).
  Proof.
    intros p Hp. pose proof B0_ge_0. pose proof (ce1_le_nb ss). pose proof (cs0_le_ce1 ss).
    cps_destruct (bucket_of a2 nb BB NB p ltac:(lia)) as (v & Hv & R).
    assert (256 * ss <= v). { destruct (Z.lt_ge_cases v (256 * ss)); [|lia]. pose proof (ClM_mono a2 nb (v + 1) (256 * ss) ltac:(lia)). unfold B0 in Hp. lia. }
    assert (v < 256 * ss + ss). { destruct (Z.lt_ge_cases v (256 * ss + ss)); [lia|]. pose proof (ClM_mono a2 nb (256 * ss + ss) v ltac:(lia)). unfold cs0 in Hp. lia. }
    exists (v - 256 * ss). split; [lia|]. replace (256 * ss + (v - 256 * ss)) with v by lia. exact R.
  Qed.
  (* [comment removed for export] *)
  Lemma tail_bucket : forall p, ce1 ss <= p < B1 -> exists c, ss < c < 256 /\ CLM (256 * ss + c) <= p < CLM (256 * ss + c + 1).
  Proof.
    intros p Hp. pose proof B0_ge_0. pose proof B1_le_nb. pose proof (cs0_le_ce1 ss). pose proof B0_le_S0.
    cps_destruct (bucket_of a2 nb BB NB p ltac:(lia)) as (v & Hv & R).
    assert (256 * ss + ss + 1 <= v). { destruct (Z.lt_ge_cases v (256 * ss + ss + 1)); [|lia]. pose proof (ClM_mono a2 nb (v + 1) (256 * ss + ss + 1) ltac:(lia)). unfold ce1 in Hp. lia. }
    assert (v < 256 * ss + 256). { destruct (Z.lt_ge_cases v (256 * ss + 256)); [lia|]. pose proof (ClM_mono a2 nb (256 * (ss + 1)) v ltac:(lia)). unfold B1 in Hp. lia. }
    exists (v - 256 * ss). split; [lia|]. replace (256 * ss + (v - 256 * ss)) with v by lia. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma reg_disjoint : forall c c' p, c <> c' -> cs0 c <= p < ce1 c -> ~ (cs0 c' <= p < ce1 c').
  Proof. intros c c' p NE Hp. unfold cs0, ce1 in *. apply (R_disjoint a2 nb (256 * c + ss)); [lia| exact Hp]. Qed.
  Lemma seed_no_reg : forall c p, 0 <= c < 256 -> B0 <= p < cs0 ss -> ~ (cs0 c <= p < ce1 c).
  Proof.
    intros c p Hc Hp R. cps_destruct (seed_bucket p Hp) as (c' & Hc' & R').
    apply (R_disjoint a2 nb (256 * ss + c') (256 * c + ss) p ltac:(nia) R'). unfold cs0, ce1 in R. exact R.
  Qed.
  Lemma tail_no_reg : forall c p, 0 <= c < 256 -> ce1 ss <= p < B1 -> ~ (cs0 c <= p < ce1 c).
  Proof.
    intros c p Hc Hp R. cps_destruct (tail_bucket p Hp) as (c' & Hc' & R').
    apply (R_disjoint a2 nb (256 * ss + c') (256 * c + ss) p ltac:(nia) R'). unfold cs0, ce1 in R. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma seed_val : forall p, B0 <= p < cs0 ss ->
    0 <= rd32 P0 p < nb /\ rd8 a2 (rd32 P0 p) = ss /\ rd8 a2 (NXT (rd32 P0 p)) < ss /\ SD (rd32 P0 p) = Some true.
  Proof.
    intros p Hp. cps_destruct (seed_bucket p Hp) as (c & Hc & R).
    destruct (P0X (256 * ss + c) ltac:(nia)) as [V _]. destruct (V p R) as [Rg K].
    destruct (proj1 (key_chars a2 nb BB (rd32 P0 p) ss c ltac:(lia)) K) as [E1 E2].
    split; [exact Rg|]. split; [exact E1|]. split; [rewrite E2; lia|].
    rewrite (SIDE_seed a2 nb NB ss); [| cbv beta; rewrite E2; lia]. f_equal. apply Z.ltb_lt. rewrite E2. lia.
  Qed.
  Lemma tail_val : forall p, ce1 ss <= p < B1 ->
    0 <= rd32 P0 p < nb /\ rd8 a2 (rd32 P0 p) = ss /\ ss < rd8 a2 (NXT (rd32 P0 p)) /\ SD (rd32 P0 p) = Some false.
  Proof.
    intros p Hp. cps_destruct (tail_bucket p Hp) as (c & Hc & R).
    destruct (P0X (256 * ss + c) ltac:(nia)) as [V _]. destruct (V p R) as [Rg K].
    destruct (proj1 (key_chars a2 nb BB (rd32 P0 p) ss c ltac:(lia)) K) as [E1 E2].
    split; [exact Rg|]. split; [exact E1|]. split; [rewrite E2; lia|].
    rewrite (SIDE_seed a2 nb NB ss); [| cbv beta; rewrite E2; lia]. f_equal. apply Z.ltb_ge. rewrite E2. lia.
  Qed.
  Lemma seed_inj : forall p q, B0 <= p < cs0 ss -> B0 <= q < cs0 ss -> rd32 P0 p = rd32 P0 q -> p = q.
  Proof.
    intros p q Hp Hq E. cps_destruct (seed_bucket p Hp) as (c & Hc & Rp). cps_destruct (seed_bucket q Hq) as (c' & Hc' & Rq).
    destruct (P0X (256 * ss + c) ltac:(nia)) as [Vp Ip]. destruct (P0X (256 * ss + c') ltac:(nia)) as [Vq _].
    pose proof (proj2 (Vp p Rp)) as Kp. pose proof (proj2 (Vq q Rq)) as Kq. rewrite E in Kp.
    assert (c = c') by lia. subst c'. apply Ip; assumption.
  Qed.
  Lemma tail_inj : forall p q, ce1 ss <= p < B1 -> ce1 ss <= q < B1 -> rd32 P0 p = rd32 P0 q -> p = q.
  Proof.
    intros p q Hp Hq E. cps_destruct (tail_bucket p Hp) as (c & Hc & Rp). cps_destruct (tail_bucket q Hq) as (c' & Hc' & Rq).
    destruct (P0X (256 * ss + c) ltac:(nia)) as [Vp Ip]. destruct (P0X (256 * ss + c') ltac:(nia)) as [Vq _].
    pose proof (proj2 (Vp p Rp)) as Kp. pose proof (proj2 (Vq q Rq)) as Kq. rewrite E in Kp.
    assert (c = c') by lia. subst c'. apply Ip; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record FWI (a1 cs : zarr) (j : Z) : Prop := {
    fw0 : forall c, 0 <= c < 256 -> cs0 c <= zget cs c /\ (zget bd c <> 0 -> zget cs c = cs0 c);
    fw1 : B0 <= j <= zget cs ss;
    fw3 : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (cs0 c <= p < zget cs c)) -> rd32 a1 p = rd32 P0 p;
    fw4 : forall c q, 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < zget cs c ->
            (0 <= rd32 a1 q < nb /\ KEY (rd32 a1 q) = 256 * c + ss /\ SD (rd32 a1 q) = Some true) /\
            (exists p', B0 <= p' < j /\ rd32 a1 p' = NXT (rd32 a1 q));
    fw5 : forall c q q', 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < zget cs c -> cs0 c <= q' < zget cs c ->
            rd32 a1 q = rd32 a1 q' -> q = q';
    fw6 : forall c k p', 0 <= c < 256 -> zget bd c = 0 -> 0 <= k < nb -> KEY k = 256 * c + ss ->
            B0 <= p' < j -> rd32 a1 p' = NXT k -> exists q, cs0 c <= q < zget cs c /\ rd32 a1 q = k }.

  (* [comment removed for export] *)
  Lemma fw_bound : forall a1 cs j, FWI a1 cs j -> forall c, 0 <= c < 256 -> zget bd c = 0 ->
    zget cs c <= cs0 c + Z.of_nat (length (Fset c true)) /\ zget cs c <= ce1 c.
  Proof.
    intros a1 cs j IV c Hc Bc.
    pose proof (proj1 (fw0 _ _ _ IV c Hc)) as L0.
    pose proof (region_le a1 (cs0 c) (zget cs c) (Fset c true) (Fset_NoDup c true) L0) as RL.
    assert (zget cs c - cs0 c <= Z.of_nat (length (Fset c true))).
    { apply RL.
      - intros q Hq. apply in_Fset. exact (proj1 (fw4 _ _ _ IV c q Hc Bc Hq)).
      - intros q q' Hq Hq'. apply (fw5 _ _ _ IV c); assumption. }
    pose proof (Fset_sum c Hc). split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fw_reg : forall a1 cs j, FWI a1 cs j -> forall c q, 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < zget cs c -> cs0 c <= q < ce1 c.
  Proof. intros a1 cs j IV c q Hc Bc Hq. pose proof (proj2 (fw_bound a1 cs j IV c Hc Bc)). lia. Qed.

  (* [comment removed for export] *)
  Lemma fw_scan : forall a1 cs j, FWI a1 cs j -> forall p, B0 <= p < zget cs ss ->
    0 <= rd32 a1 p < nb /\ rd8 a2 (rd32 a1 p) = ss /\ SD (rd32 a1 p) = Some true /\
    (p < cs0 ss -> rd32 a1 p = rd32 P0 p) /\ (cs0 ss <= p -> KEY (rd32 a1 p) = 256 * ss + ss).
  Proof.
    intros a1 cs j IV p Hp.
    destruct (Z.lt_ge_cases p (cs0 ss)) as [L|G].
    - assert (E : rd32 a1 p = rd32 P0 p).
      { apply (fw3 _ _ _ IV). intros c Hc Bc R. apply (seed_no_reg c p Hc ltac:(lia)). exact (fw_reg a1 cs j IV c p Hc Bc R). }
      rewrite E. cps_destruct (seed_val p ltac:(lia)) as (R1 & R2 & R3 & R4). repeat split; try assumption; try lia.
    - cps_destruct (proj1 (fw4 _ _ _ IV ss p SS BD ltac:(lia))) as (R1 & R2 & R3).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 p) ss ss SS) R2) as [E1 E2].
      repeat split; try assumption; try lia.
  Qed.

  Lemma fw_scan_inj : forall a1 cs j, FWI a1 cs j -> forall p q, B0 <= p < zget cs ss -> B0 <= q < zget cs ss ->
    rd32 a1 p = rd32 a1 q -> p = q.
  Proof.
    intros a1 cs j IV p q Hp Hq E.
    cps_destruct (fw_scan a1 cs j IV p Hp) as (_ & _ & _ & Sp & Fp). cps_destruct (fw_scan a1 cs j IV q Hq) as (_ & _ & _ & Sq & Fq).
    destruct (Z.lt_ge_cases p (cs0 ss)) as [Lp|Gp]; destruct (Z.lt_ge_cases q (cs0 ss)) as [Lq|Gq].
    - apply seed_inj; try lia; (rewrite <- Sp, <- Sq by lia; exact E).
    - exfalso. cps_destruct (seed_val p ltac:(lia)) as (_ & _ & R3 & _). specialize (Fq Gq).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 q) ss ss SS) Fq) as [_ E2]. rewrite <- E, Sp in E2 by lia. cbv beta in R3. lia.
    - exfalso. cps_destruct (seed_val q ltac:(lia)) as (_ & _ & R3 & _). specialize (Fp Gp).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 p) ss ss SS) Fp) as [_ E2]. rewrite E, Sq in E2 by lia. cbv beta in R3. lia.
    - apply (fw5 _ _ _ IV ss); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FWI_init : forall cs, (forall c, 0 <= c < 256 -> zget cs c = cs0 c) -> FWI P0 cs B0.
  Proof.
    intros cs H. pose proof B0_le_S0. constructor.
    - intros c Hc. rewrite H by lia. split; [lia| intros; reflexivity].
    - rewrite (H ss SS). lia.
    - intros; reflexivity.
    - intros c q Hc Bc Hq. rewrite H in Hq by lia. lia.
    - intros c q q' Hc Bc Hq. rewrite H in Hq by lia. lia.
    - intros c k p' Hc Bc Hk Kk Hp'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FWI_step : forall a1 cs j, FWI a1 cs j -> j < zget cs ss ->
    let u := rd32 a1 j in let k := PRV u in let c1 := rd8 a2 k in
    0 <= u < nb /\ 0 <= k < nb /\ 0 <= c1 < 256 /\ KEY k = 256 * c1 + ss /\
    (zget bd c1 = 0 -> cs0 c1 <= zget cs c1 < ce1 c1 /\
       FWI (wr32 a1 (zget cs c1) k) (zset cs c1 (zget cs c1 + 1)) (j + 1)) /\
    (zget bd c1 <> 0 -> FWI a1 cs (j + 1)).
  Proof.
    intros a1 cs j IV LT. cbv zeta.
    pose proof (fw1 _ _ _ IV) as J.
    cps_destruct (fw_scan a1 cs j IV j ltac:(lia)) as (Ru & Bu & Su & _ & _).
    set (u := rd32 a1 j) in *.
    pose proof (prv_range nb NB u Ru) as Rk. set (k := PRV u) in *.
    pose proof (BB k) as Rc. set (c1 := rd8 a2 k) in *.
    assert (Ek : NXT k = u) by (subst k; apply nxt_prv; exact Ru).
    assert (Kk : KEY k = 256 * c1 + ss). { apply (proj2 (key_chars a2 nb BB k c1 ss SS)). split; [reflexivity| rewrite Ek; exact Bu]. }
    assert (Sk : SD k = Some true). { rewrite (SIDE_nxt a2 nb NB ss NA k Rk) by (rewrite Ek; exact Bu). rewrite Ek. exact Su. }
    split; [exact Ru|]. split; [exact Rk|]. split; [exact Rc|]. split; [exact Kk|]. split.
    - (* [comment removed for export] *)
      intros Bc1.
      pose proof (fw0 _ _ _ IV c1 Rc) as [L0 _].
      set (w := zget cs c1) in *. assert (Ew : w = zget cs c1) by reflexivity.
      (* [comment removed for export] *)
      assert (NEW : forall q, cs0 c1 <= q < w -> rd32 a1 q <> k).
      { intros q Hq E. cps_destruct (proj2 (fw4 _ _ _ IV c1 q Rc Bc1 Hq)) as (p' & Hp' & Ep').
        rewrite E, Ek in Ep'. pose proof (fw_scan_inj a1 cs j IV p' j ltac:(lia) ltac:(lia) Ep'). lia. }
      (* [comment removed for export] *)
      assert (FIT : w < ce1 c1).
      { pose proof (region_lt a1 (cs0 c1) w (Fset c1 true) k (Fset_NoDup c1 true) L0
                      ltac:(apply in_Fset; split; [exact Rk| split; [exact Kk| exact Sk]])) as RL.
        pose proof (Fset_sum c1 Rc).
        assert (w - cs0 c1 + 1 <= Z.of_nat (length (Fset c1 true))); [|lia].
        apply RL.
        - intros q Hq. split; [apply in_Fset; exact (proj1 (fw4 _ _ _ IV c1 q Rc Bc1 Hq))| apply NEW; exact Hq].
        - intros q q' Hq Hq'. apply (fw5 _ _ _ IV c1); assumption. }
      split; [split; [exact L0| exact FIT]|].
      (* [comment removed for export] *)
      assert (W1 : forall p, B0 <= p < zget cs ss -> p <> w).
      { intros p Hp E. subst p. destruct (Z.eq_dec c1 ss) as [E1|N1].
        - subst w. rewrite E1 in Hp. lia.
        - destruct (Z.lt_ge_cases w (cs0 ss)) as [Lw|Gw].
          + apply (seed_no_reg c1 w Rc ltac:(lia)). split; [exact L0| exact FIT].
          + apply (reg_disjoint ss c1 w ltac:(congruence) (fw_reg a1 cs j IV ss w SS BD ltac:(lia))). split; [exact L0| exact FIT]. }
      assert (WQ : forall c q, 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < zget cs c -> q <> w).
      { intros c q Hc Bc Hq E. subst q. destruct (Z.eq_dec c c1) as [->|NE]; [lia|].
        apply (reg_disjoint c c1 w NE (fw_reg a1 cs j IV c w Hc Bc Hq)). split; [exact L0| exact FIT]. }
      assert (RD : forall p, p <> w -> rd32 (wr32 a1 w k) p = rd32 a1 p) by (intros; apply rd32_wr32_other; assumption).
      assert (RW : rd32 (wr32 a1 w k) w = k) by (apply rd32_wr32_same; lia).
      assert (CS : forall c, zget (zset cs c1 (w + 1)) c = (if c =? c1 then w + 1 else zget cs c)) by (intros; apply zget_zset).
      constructor.
      + intros c Hc. rewrite CS. destruct (Z.eqb_spec c c1) as [->|NE]; [| exact (fw0 _ _ _ IV c Hc)].
        split; [lia| intros X; exfalso; exact (X Bc1)].
      + rewrite CS. destruct (Z.eqb_spec ss c1) as [E|NE]; [subst w; rewrite <- E; lia| lia].
      + intros p Hp. rewrite RD.
        * apply (fw3 _ _ _ IV). intros c Hc Bc R. apply (Hp c Hc Bc). rewrite CS. destruct (Z.eqb_spec c c1) as [->|NE]; lia.
        * intros E. subst p. apply (Hp c1 Rc Bc1). rewrite CS, Z.eqb_refl. lia.
      + intros c q Hc Bc Hq. rewrite CS in Hq.
        destruct (Z.eqb_spec c c1) as [->|NE].
        * destruct (Z.eq_dec q w) as [->|NQ].
          -- rewrite RW. split; [split; [exact Rk| split; [exact Kk| exact Sk]]|].
             exists j. split; [lia|]. rewrite RD by (apply W1; lia). symmetry. exact Ek.
          -- assert (Hq' : cs0 c1 <= q < w) by lia. rewrite (RD q NQ).
             destruct (fw4 _ _ _ IV c1 q Rc Bc1 Hq') as [X (p' & Hp' & E')]. split; [exact X|].
             exists p'. split; [lia|]. rewrite RD by (apply W1; lia). exact E'.
        * rewrite (RD q (WQ c q Hc Bc Hq)).
          destruct (fw4 _ _ _ IV c q Hc Bc Hq) as [X (p' & Hp' & E')]. split; [exact X|].
          exists p'. split; [lia|]. rewrite RD by (apply W1; lia). exact E'.
      + intros c q q' Hc Bc Hq Hq' E. rewrite CS in Hq, Hq'.
        destruct (Z.eqb_spec c c1) as [->|NE].
        * destruct (Z.eq_dec q w) as [->|NQ], (Z.eq_dec q' w) as [->|NQ']; [reflexivity| | |].
          -- exfalso. rewrite RW, (RD q' NQ') in E. apply (NEW q' ltac:(lia)). symmetry. exact E.
          -- exfalso. rewrite RW, (RD q NQ) in E. apply (NEW q ltac:(lia)). exact E.
          -- rewrite (RD q NQ), (RD q' NQ') in E. apply (fw5 _ _ _ IV c1 q q' Rc Bc1 ltac:(lia) ltac:(lia) E).
        * rewrite (RD q (WQ c q Hc Bc Hq)), (RD q' (WQ c q' Hc Bc Hq')) in E. apply (fw5 _ _ _ IV c q q' Hc Bc Hq Hq' E).
      + intros c k' p' Hc Bc Hk' Kk' Hp' E'. rewrite CS. rewrite RD in E' by (apply W1; lia).
        destruct (Z.eq_dec p' j) as [->|NP].
        * assert (k' = k). { apply (nxt_inj nb k' k Hk' Rk). rewrite Ek. fold u in E'. rewrite <- E'. reflexivity. }
          subst k'. rewrite Kk in Kk'. assert (c = c1) by lia. subst c. rewrite Z.eqb_refl.
          exists w. split; [lia| exact RW].
        * cps_destruct (fw6 _ _ _ IV c k' p' Hc Bc Hk' Kk' ltac:(lia) E') as (q & Hq & Eq).
          exists q. split; [destruct (Z.eqb_spec c c1) as [->|NE]; lia|]. rewrite (RD q (WQ c q Hc Bc Hq)). exact Eq.
    - intros Bc1. constructor.
      + exact (fw0 _ _ _ IV).
      + lia.
      + exact (fw3 _ _ _ IV).
      + intros c q Hc Bc Hq. destruct (fw4 _ _ _ IV c q Hc Bc Hq) as [X (p' & Hp' & E')]. split; [exact X|]. exists p'. split; [lia| exact E'].
      + exact (fw5 _ _ _ IV).
      + intros c k' p' Hc Bc Hk' Kk' Hp' E'. destruct (Z.eq_dec p' j) as [->|NE].
        * exfalso. assert (k' = k). { apply (nxt_inj nb k' k Hk' Rk). rewrite Ek. fold u in E'. rewrite <- E'. reflexivity. }
          subst k'. rewrite Kk in Kk'. assert (c = c1) by lia. subst c. exact (Bc1 Bc).
        * apply (fw6 _ _ _ IV c k' p'); try assumption. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prv_model' : forall u, 0 <= u < nb -> (if u - 1 <? 0 then u - 1 + nb else u - 1) = PRV u.
  Proof. intros u Hu. pose proof (prv_model nb NB u Hu) as H. cbv zeta in H. exact H. Qed.

  Lemma FWI_loop : forall f a1 cs j, FWI a1 cs j -> nb - j < Z.of_nat f ->
    let r := ms_copy_fwd f a1 cs a2r bd nb ss j in
    FWI (fst (fst r)) (snd (fst r)) (snd r) /\ snd r = zget (snd (fst r)) ss.
  Proof.
    induction f as [|f IH]; intros a1 cs j IV Hf; cbv zeta.
    - exfalso. pose proof (fw1 _ _ _ IV). pose proof (proj2 (fw_bound a1 cs j IV ss SS BD)). pose proof (ce1_le_nb ss). cbn in Hf. lia.
    - rewrite ms_copy_fwd_S. destruct (Z.ltb_spec j (zget cs ss)) as [LT|GE].
      + pose proof (FWI_step a1 cs j IV LT) as ST. cbv zeta in ST. cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
        cbv zeta. rewrite (prv_model' (rd32 a1 j) Ru). rewrite (AGR (PRV (rd32 a1 j)) Rk).
        destruct (Z.eqb_spec (zget bd (rd8 a2 (PRV (rd32 a1 j)))) 0) as [Bz|Bnz].
        * destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j + 1) IV'). lia.
        * apply (IH a1 cs (j + 1) (CASE1 Bnz)). lia.
      + cbn [fst snd]. split; [exact IV|]. pose proof (fw1 _ _ _ IV). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FW_all_scanned : forall a1 cs X, FWI a1 cs X -> X = zget cs ss ->
    forall n u, 0 <= u < nb -> rd8 a2 u = ss -> side a2 nb ss n u = Some true -> exists p, B0 <= p < X /\ rd32 a1 p = u.
  Proof.
    intros a1 cs X IV HX. induction n as [|n IH]; intros u Hu Bu Hs; [cbn in Hs; discriminate|].
    rewrite (side_S a2 nb ss) in Hs. cbv beta in Hs.
    destruct (Z.eqb_spec (rd8 a2 (NXT u)) ss) as [Bn|Bn].
    - cps_destruct (IH (NXT u) (nxt_range nb NB u Hu) Bn Hs) as (p' & Hp' & E').
      assert (Ku : KEY u = 256 * ss + ss) by (apply (proj2 (key_chars a2 nb BB u ss ss SS)); split; assumption).
      cps_destruct (fw6 _ _ _ IV ss u p' SS BD Hu Ku ltac:(lia) E') as (q & Hq & Eq).
      exists q. split; [| exact Eq]. pose proof B0_le_S0. unfold cs0 in *. lia.
    - injection Hs as Hs'. apply Z.ltb_lt in Hs'. pose proof (BB (NXT u)) as Bc.
      set (c := rd8 a2 (NXT u)) in *.
      assert (Ku : KEY u = 256 * ss + c) by (apply (proj2 (key_chars a2 nb BB u ss c ltac:(lia))); split; [assumption| reflexivity]).
      cps_destruct (BEX_cover a2 nb NB P0 (256 * ss + c) (P0X (256 * ss + c) ltac:(nia)) u Hu Ku) as (p & Hp & Ep).
      assert (Rp : B0 <= p < cs0 ss).
      { unfold B0, cs0. pose proof (ClM_mono a2 nb (256 * ss) (256 * ss + c) ltac:(lia)).
        pose proof (ClM_mono a2 nb (256 * ss + c + 1) (256 * ss + ss) ltac:(lia)). lia. }
      exists p. pose proof (fw1 _ _ _ IV). pose proof (proj1 (fw0 _ _ _ IV ss SS)). split; [unfold cs0 in *; lia|].
      rewrite <- Ep. apply (fw3 _ _ _ IV). intros c' Hc' Bc' R. apply (seed_no_reg c' p Hc' Rp). exact (fw_reg a1 cs X IV c' p Hc' Bc' R).
  Qed.

  (* [comment removed for export] *)
  Lemma FW_regions : forall a1 cs X, FWI a1 cs X -> X = zget cs ss ->
    forall c, 0 <= c < 256 -> zget bd c = 0 ->
      zget cs c = cs0 c + Z.of_nat (length (Fset c true)) /\
      (forall q, cs0 c <= q < zget cs c -> In (rd32 a1 q) (Fset c true)) /\
      (forall q q', cs0 c <= q < zget cs c -> cs0 c <= q' < zget cs c -> rd32 a1 q = rd32 a1 q' -> q = q') /\
      (forall k, In k (Fset c true) -> exists q, cs0 c <= q < zget cs c /\ rd32 a1 q = k).
  Proof.
    intros a1 cs X IV HX c Hc Bc.
    assert (IN : forall q, cs0 c <= q < zget cs c -> In (rd32 a1 q) (Fset c true)).
    { intros q Hq. apply in_Fset. exact (proj1 (fw4 _ _ _ IV c q Hc Bc Hq)). }
    assert (INJ : forall q q', cs0 c <= q < zget cs c -> cs0 c <= q' < zget cs c -> rd32 a1 q = rd32 a1 q' -> q = q').
    { intros q q'. apply (fw5 _ _ _ IV c); assumption. }
    assert (COV : forall k, In k (Fset c true) -> exists q, cs0 c <= q < zget cs c /\ rd32 a1 q = k).
    { intros k Hk. apply in_Fset in Hk. cps_destruct Hk as (Rk & Kk & Sk).
      destruct (proj1 (key_chars a2 nb BB k c ss SS) Kk) as [_ Bn].
      pose proof (SIDE_nxt a2 nb NB ss NA k Rk Bn) as SN. cbv beta in SN. rewrite Sk in SN.
      cps_destruct (FW_all_scanned a1 cs X IV HX (Z.to_nat nb) (NXT k) (nxt_range nb NB k Rk) Bn (eq_sym SN)) as (p & Hp & Ep).
      exact (fw6 _ _ _ IV c k p Hc Bc Rk Kk Hp Ep). }
    split; [| split; [exact IN| split; [exact INJ| exact COV]]].
    pose proof (region_eq a1 (cs0 c) (zget cs c) (Fset c true) (Fset_NoDup c true) (proj1 (fw0 _ _ _ IV c Hc)) IN INJ COV). lia.
  Qed.

  (* [comment removed for export] *)
  Definition csF (c : Z) : Z := cs0 c + Z.of_nat (length (Fset c true)).

  Record FWPOST (a1 cs : zarr) : Prop := {
    fp_cs : forall c, 0 <= c < 256 -> zget cs c = (if zget bd c =? 0 then csF c else cs0 c);
    fp_frame : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (cs0 c <= p < csF c)) -> rd32 a1 p = rd32 P0 p;
    fp_in : forall c q, 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < csF c -> In (rd32 a1 q) (Fset c true);
    fp_inj : forall c q q', 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < csF c -> cs0 c <= q' < csF c -> rd32 a1 q = rd32 a1 q' -> q = q';
    fp_cov : forall c k, 0 <= c < 256 -> zget bd c = 0 -> In k (Fset c true) -> exists q, cs0 c <= q < csF c /\ rd32 a1 q = k }.

  Lemma csF_le_ce1 : forall c, 0 <= c < 256 -> cs0 c <= csF c <= ce1 c.
  Proof. intros c Hc. unfold csF. pose proof (Fset_sum c Hc). lia. Qed.

  Theorem forward_scan : forall cs, (forall c, 0 <= c < 256 -> zget cs c = cs0 c) ->
    let r := ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0 in
    FWPOST (fst (fst r)) (snd (fst r)) /\ snd r = zget (snd (fst r)) ss.
  Proof.
    intros cs Hcs. cbv zeta.
    pose proof (FWI_loop (S (Z.to_nat nb)) P0 cs B0 (FWI_init cs Hcs) ltac:(pose proof B0_ge_0; lia)) as L. cbv zeta in L.
    destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[a1 cs'] X]. cbn [fst snd] in *. destruct L as [IV HX].
    split; [| exact HX].
    assert (CS : forall c, 0 <= c < 256 -> zget bd c = 0 -> zget cs' c = csF c).
    { intros c Hc Bc. exact (proj1 (FW_regions a1 cs' X IV HX c Hc Bc)). }
    constructor.
    - intros c Hc. destruct (Z.eqb_spec (zget bd c) 0) as [Bc|Bc]; [apply CS; assumption|]. apply (proj2 (fw0 _ _ _ IV c Hc)). exact Bc.
    - intros p Hp. apply (fw3 _ _ _ IV). intros c Hc Bc. rewrite CS by assumption. apply Hp; assumption.
    - intros c q Hc Bc Hq. rewrite <- CS in Hq by assumption. exact (proj1 (proj2 (FW_regions a1 cs' X IV HX c Hc Bc)) q Hq).
    - intros c q q' Hc Bc Hq Hq'. rewrite <- CS in Hq, Hq' by assumption. exact (proj1 (proj2 (proj2 (FW_regions a1 cs' X IV HX c Hc Bc))) q q' Hq Hq').
    - intros c k Hc Bc Hk. rewrite <- CS by assumption. exact (proj2 (proj2 (proj2 (FW_regions a1 cs' X IV HX c Hc Bc))) k Hk).
  Qed.
End Copy.
