(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnDivLoop BnDivSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lval_norm_ge : forall V dn, limbs V -> length V = dn -> (1 <= dn)%nat -> 2 ^ 63 <= nth (dn - 1) V 0 ->
  Bp (dn - 1) * 2 ^ 63 <= lval V.
Proof.
  intros V dn HV LV Hdn Htop.
  pose proof (nth_limb_val V (dn - 1) HV ltac:(lia)) as E.
  pose proof (lval_nonneg _ (limbs_firstn (dn - 1) V HV)). pose proof (lval_nonneg _ (limbs_skipn (S (dn - 1)) V HV)).
  pose proof (Bp_pos (dn - 1)). pose proof (Bp_pos (S (dn - 1))). nia.
Qed.

Lemma lshift_full_val : forall l sh, limbs l -> 0 <= sh < 64 ->
  lval (fst (lshift_limbs l sh 0) ++ [snd (lshift_limbs l sh 0)]) = lval l * 2 ^ sh.
Proof.
  intros l sh Hl Hsh.
  pose proof (lshift_limbs_spec l sh 0 Hl Hsh ltac:(split; [lia| apply Z.pow_pos_nonneg; lia])) as S.
  destruct (lshift_limbs l sh 0) as [r mo]. cbn [fst snd]. destruct S as (_ & Lr & _ & V).
  rewrite lval_app, lval_single, Lr. lia.
Qed.

Lemma div_top_init : forall (snumbuf numl V : list Z) (sh : Z) (dn tn nP : nat),
  limbs snumbuf -> (nP <= length snumbuf)%nat -> (1 <= dn)%nat -> (dn + 1 <= nP)%nat -> (tn + 1 <= nP)%nat ->
  0 <= sh < 64 -> limbs numl -> length numl = tn ->
  firstn nP snumbuf = (if (tn =? 0)%nat then [0] else fst (lshift_limbs numl sh 0) ++ [snd (lshift_limbs numl sh 0)]) ++ repeat 0 (nP - (tn + 1)) ->
  limbs V -> length V = dn -> 2 ^ 63 <= nth (dn - 1) V 0 ->
  lval (slice snumbuf (nP - dn) dn) < lval V.
Proof.
  intros snumbuf numl V sh dn tn nP Hs Hlen Hdn HnP Htn Hsh Hnl Lnl FNP HV LV Htop.
  apply (div_top_cond snumbuf (nP - dn) dn tn (lval V)); try assumption; try lia.
  - replace (nP - dn + dn)%nat with nP by lia. rewrite FNP, lval_app, lval_repeat0, Z.mul_0_r, Z.add_0_r.
    destruct (Nat.eqb_spec tn 0) as [Z0|NZ].
    + rewrite Z0. cbn [lval]. rewrite Bp_0. lia.
    + rewrite lshift_full_val by assumption.
      pose proof (lval_bound numl Hnl) as BL. rewrite Lnl in BL.
      assert (0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ sh <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
      pose proof (Bp_pos tn). nia.
  - apply lval_norm_ge; assumption.
Qed.
