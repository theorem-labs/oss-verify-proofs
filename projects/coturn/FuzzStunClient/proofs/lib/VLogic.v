(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record venv := mkEnv {
  e_sp0 : Z ; e_data : Z ; e_size : Z ; e_ra : Z ; e_tp : Z ; e_gp : Z ;
  e_sregs : list Z                (* [comment removed for export] *)
}.

Definition fix_val (E : venv) (s : sym) : option Z :=
  if Pos.eqb s SP0 then Some (e_sp0 E)
  else if Pos.eqb s DATA then Some (e_data E)
  else if Pos.eqb s SIZE then Some (e_size E)
  else if Pos.eqb s RA then Some (e_ra E)
  else if Pos.eqb s TP then Some (e_tp E)
  else if Pos.eqb s GP then Some (e_gp E)
  else if Pos.leb 5 s && Pos.leb s 16 then nth_error (e_sregs E) (Pos.to_nat s - 5)
  else None.

Definition gamma_fix (E : venv) (nu : val) : Prop :=
  forall s z, fix_val E s = Some z -> nu s = z.

Lemma fix_val_fixed E s z : fix_val E s = Some z -> (s <= LAST_FIXED)%positive.
Proof.
  unfold fix_val, SP0, DATA, SIZE, RA, TP, GP, LAST_FIXED. intros H.
  destruct (Pos.leb_spec s 63) as [Hle|Hgt]; [exact Hle|exfalso].
  rewrite (proj2 (Pos.eqb_neq s 1)) in H by lia.
  rewrite (proj2 (Pos.eqb_neq s 2)) in H by lia.
  rewrite (proj2 (Pos.eqb_neq s 3)) in H by lia.
  rewrite (proj2 (Pos.eqb_neq s 4)) in H by lia.
  rewrite (proj2 (Pos.eqb_neq s 17)) in H by lia.
  rewrite (proj2 (Pos.eqb_neq s 18)) in H by lia.
  destruct (Pos.leb_spec 5 s); destruct (Pos.leb_spec s 16); simpl in H; try discriminate. lia.
Qed.

(* [comment removed for export] *)
Definition cond_holds (k : ckind) (x y : Z) : bool :=
  match k with
  | CK_lt => Z.ltb (zswrap 64 x) (zswrap 64 y)
  | CK_ltu => Z.ltb (zwrap 64 x) (zwrap 64 y)
  | CK_eq => Z.eqb (zwrap 64 x) (zwrap 64 y)
  end.

Definition gamma_conddef (nu : val) (A : vstate) : Prop :=
  forall b k x y, pm_get b (vs_conddef A) = Some (k, x, y) ->
    nu b = (if cond_holds k (eval nu x) (eval nu y) then 1 else 0).

Definition gamma_moddef (nu : val) (A : vstate) : Prop :=
  forall r x m, pm_get r (vs_moddef A) = Some (x, m) -> 0 < m /\ nu r = (eval nu x) mod m.

Definition gamma_valset (nu : val) (A : vstate) : Prop :=
  forall s vs, pm_get s (vs_valset A) = Some vs -> In (nu s) vs.

(* [comment removed for export] *)
Definition regs_below (A : vstate) : Prop :=
  forall r e, pm_get r (vs_regs A) = Some e -> lin_below e (vs_next A) = true.
Definition cells_below (m : cellmap) (b : positive) : Prop :=
  forall k w e, In (k, (w, Some e)) m -> lin_below e b = true.
Definition side_below (A : vstate) : Prop :=
  (forall b k x y, pm_get b (vs_conddef A) = Some (k, x, y) ->
      (b < vs_next A)%positive /\ lin_below x (vs_next A) = true /\ lin_below y (vs_next A) = true)
  /\ (forall r x m, pm_get r (vs_moddef A) = Some (x, m) ->
      (r < vs_next A)%positive /\ lin_below x (vs_next A) = true)
  /\ (forall s vs, pm_get s (vs_valset A) = Some vs -> (s < vs_next A)%positive).
Definition state_below (A : vstate) : Prop :=
  (LAST_FIXED < vs_next A)%positive /\
  store_below (vs_store A) (vs_next A) = true /\ regs_below A /\
  cells_below (vs_slots A) (vs_next A) /\ cells_below (vs_globs A) (vs_next A) /\ side_below A.

(* [comment removed for export] *)
Definition lgamma (A : vstate) (nu : val) : Prop :=
  sat nu (vs_store A) /\ gamma_conddef nu A /\ gamma_moddef nu A /\ gamma_valset nu A /\ state_below A.

(* [comment removed for export] *)
Definition ext (b : positive) (nu nu' : val) : Prop :=
  forall s, (s < b)%positive -> nu' s = nu s.

Lemma ext_refl b nu : ext b nu nu.
Proof. intros s _; reflexivity. Qed.

Lemma ext_trans b1 b2 nu1 nu2 nu3 :
  (b1 <= b2)%positive -> ext b1 nu1 nu2 -> ext b2 nu2 nu3 -> ext b1 nu1 nu3.
Proof. intros Hle H1 H2 s Hs. rewrite H2 by lia. apply H1; lia. Qed.

Lemma ext_mono b1 b2 nu nu' : (b1 <= b2)%positive -> ext b2 nu nu' -> ext b1 nu nu'.
Proof. intros Hle H s Hs. apply H. lia. Qed.

Lemma eval_ext_below b nu nu' e :
  ext b nu nu' -> lin_below e b = true -> eval nu' e = eval nu e.
Proof.
  intros Hext Hb. apply eval_ext. intros s Hs. apply Hext.
  exact (proj1 (lin_below_iff e b) Hb s Hs).
Qed.

Lemma lin_below_mono e b b' : (b <= b')%positive -> lin_below e b = true -> lin_below e b' = true.
Proof.
  intros Hle H. apply (proj2 (lin_below_iff e b')). intros s Hs.
  pose proof (proj1 (lin_below_iff e b) H s Hs). lia.
Qed.

Lemma gamma_fix_ext E b nu nu' :
  (LAST_FIXED < b)%positive -> ext b nu nu' -> gamma_fix E nu -> gamma_fix E nu'.
Proof.
  intros Hb Hext H s z Hs. rewrite Hext; [auto|]. pose proof (fix_val_fixed E s z Hs). lia.
Qed.
