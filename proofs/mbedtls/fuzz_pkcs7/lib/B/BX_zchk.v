From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr.
Import ListNotations.
Open Scope Z_scope.

Lemma zchk_land1 x : Z.land x 1 = x mod 2. Proof. apply (Z.land_ones x 1); lia. Qed.
Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Lemma zchk_land15 x : Z.land x 15 = x mod 16. Proof. apply (Z.land_ones x 4); lia. Qed.

Lemma zchk_lor_mod (a b k : Z) : 0 <= k -> a mod 2 ^ k = 0 -> b mod 2 ^ k = 0 -> Z.land (Z.lor a b) (Z.ones k) = 0.
Proof.
  intros K A B. rewrite Z.land_lor_distr_l, !Z.land_ones by exact K. rewrite A, B. reflexivity.
Qed.
Lemma zchk_lor3 a b : a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof. intros A B. apply (zchk_lor_mod a b 2); [lia | exact A | exact B]. Qed.
Lemma zchk_lor7 a b : a mod 8 = 0 -> b mod 8 = 0 -> Z.land (Z.lor a b) 7 = 0.
Proof. intros A B. apply (zchk_lor_mod a b 3); [lia | exact A | exact B]. Qed.

Lemma zchk_signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.lt_ge_cases z 0).
  - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
Qed.

Ltac zchk_fails := constr:(@nil Z).
Ltac zchk_new := constr:(@nil Z).
Ltac zchk_unpin := idtac.

Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Ltac zlia := try zchk_unpin; zchk_clear; lia.

Ltac zchk_false :=
  repeat match goal with H : context [Z.land ?x 7] |- _ => rewrite (zchk_land7 x) in H end;
  repeat match goal with H : context [Z.land ?x 3] |- _ => rewrite (zchk_land3 x) in H end;
  repeat match goal with H : context [Z.land ?x 1] |- _ => rewrite (zchk_land1 x) in H end;
  repeat match goal with H : context [Z.land ?x 15] |- _ => rewrite (zchk_land15 x) in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => unfold zlow in H; destruct (Z.eqb_spec a b); cbn in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => destruct (Z.eqb_spec a b); cbn in H end;
  try discriminate; unfold zlow in *; zlia.

Ltac zchk_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; zlia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; zlia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; zlia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; zlia) ]
  end.
Ltac zchk_base :=
  first [ reflexivity
        | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
        | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => zchk_base
  end.
Ltac zchk_solve :=
  repeat match goal with |- context [Z.land (Z.lor ?a ?b) 3] => rewrite (zchk_lor3 a b) by zlia end;
  repeat match goal with |- context [Z.land (Z.lor ?a ?b) 7] => rewrite (zchk_lor7 a b) by zlia end;
  rewrite ?zchk_land1, ?zchk_land3, ?zchk_land7, ?zchk_land15;
  zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with
                 | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
                 | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (zchk_signed_lit64 x) by zlia
                 end;
          zchk_rec ].

Ltac zchk_if :=
  let tr := zchk_fails in
  match goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 ?t else _) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb t) tr) with true =>
        replace c with false; [cbv_concl_iota | symmetry; zchk_solve] end
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 ?t) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb t) tr) with true =>
        replace c with true; [cbv_concl_iota | symmetry; zchk_solve] end
  end.
Ltac zabsorb :=
  let l := zchk_new in
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) l) with true => step; zsimp end
  end.
Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
