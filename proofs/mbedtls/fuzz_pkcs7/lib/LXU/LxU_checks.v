(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp.bitvector Require Import definitions.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxStep LxRun LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
Import ListNotations.
Open Scope Z_scope.

Lemma lxu_land_ones : forall x k, 0 <= k -> Z.land x (2 ^ k - 1) = x mod 2 ^ k.
Proof. intros x k Hk. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma lxu_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (lxu_land_ones x 1 ltac:(lia)). Qed.
Lemma lxu_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (lxu_land_ones x 2 ltac:(lia)). Qed.
Lemma lxu_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (lxu_land_ones x 3 ltac:(lia)). Qed.
Lemma lxu_land15 : forall x, Z.land x 15 = x mod 16.
Proof. intros x. exact (lxu_land_ones x 4 ltac:(lia)). Qed.

Lemma lxu_lxor_b2z : forall b1 b2, Z.lxor (Z.b2z b1) (Z.b2z b2) = Z.b2z (xorb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma lxu_land_b2z : forall b1 b2, Z.land (Z.b2z b1) (Z.b2z b2) = Z.b2z (andb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma lxu_lor_b2z : forall b1 b2, Z.lor (Z.b2z b1) (Z.b2z b2) = Z.b2z (orb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma lxu_shiftr_div : forall x k, 0 <= k -> Z.shiftr x k = x / 2 ^ k.
Proof. intros x k Hk. apply Z.shiftr_div_pow2. exact Hk. Qed.

Lemma lxu_bvu_range : forall (w : bv 64), 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Ltac lxu_colZ t :=
  lazymatch t with
  | Z.land ?a ?k => tryif lx_is_lit k then lxu_colZ a else lx_addZ t
  | Z.add ?a ?b => lxu_colZ a; lxu_colZ b
  | Z.sub ?a ?b => lxu_colZ a; lxu_colZ b
  | Z.opp ?a => lxu_colZ a
  | Z.mul ?c ?a => tryif lx_is_lit c then lxu_colZ a
                  else tryif lx_is_klit a then (lxu_colZ c; lx_addZ t)
                  else tryif lx_is_klit c then (lxu_colZ a; lx_addZ t)
                  else (lxu_colZ c; lxu_colZ a)
  | Z.shiftr ?a ?k => tryif lx_is_lit k then lxu_colZ a else lx_addZ t
  | bv_unsigned ?w => lx_addW w
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => tryif (lx_is_lit a; lx_is_lit b) then idtac else lx_addZ t
  | _ => lx_addZ t
  end.

Ltac lxu_reZ t :=
  lazymatch t with
  | Z.land ?a ?k => lazymatch k with
                    | Zpos _ => let x := lxu_reZ a in constr:(EOp OAnd x (ELit k))
                    | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
                    end
  | Z.add ?a ?b => let x := lxu_reZ a in let y := lxu_reZ b in constr:(EAdd x y)
  | Z.sub ?a ?b => let x := lxu_reZ a in let y := lxu_reZ b in constr:(EAdd x (EMulC (-1) y))
  | Z.opp ?a => let x := lxu_reZ a in constr:(EMulC (-1) x)
  | Z.mul ?c ?a =>
      lazymatch c with
      | Z0 => let x := lxu_reZ a in constr:(EMulC c x)
      | Zpos _ => let x := lxu_reZ a in constr:(EMulC c x)
      | Zneg _ => let x := lxu_reZ a in constr:(EMulC c x)
      | _ => lazymatch a with
             | Z0 => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Zpos _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Zneg _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Z.pow (Zpos _) (Zpos _) => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | _ => lazymatch c with
                    | Z.pow (Zpos _) (Zpos _) => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
                    | _ => let x := lxu_reZ c in let y := lxu_reZ a in constr:(EOp OMul x y)
                    end
             end
      end
  | Z.shiftr ?a ?k =>
      lazymatch k with
      | Zpos _ => let x := lxu_reZ a in constr:(EOp OShr x (ELit k))
      | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
      end
  | bv_unsigned ?w => let l := lx_getW in let i := lx_idx w l in constr:(EUv i)
  | Z0 => constr:(ELit 0) | Zpos _ => constr:(ELit t) | Zneg _ => constr:(ELit t)
  | Z.pow ?a ?b =>
      lazymatch a with
      | Zpos _ => lazymatch b with
                  | Zpos _ => let v := eval cbv in t in constr:(ELit v)
                  | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
                  end
      | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
      end
  | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
  end.

Ltac lxu_keep_arith :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail | @eq bool _ _ => fail
      | _ \/ _ => fail | _ /\ _ => fail
      | _ => lazymatch type of T with Prop => clear H end
      end
  end.

Ltac lxu_bvu_ranges :=
  repeat match goal with
  | H : context [bv_unsigned ?w] |- _ =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned w < 2 ^ 64 |- _ => fail
      | |- _ => pose proof (lxu_bvu_range w)
      end
  end.

Ltac lxu_norm :=
  rewrite ?lx_bvu64 in *;
  rewrite ?lxu_land1, ?lxu_land3, ?lxu_land7, ?lxu_land15 in *;
  rewrite ?lxu_lxor_b2z, ?lxu_land_b2z, ?lxu_lor_b2z in *;
  repeat match goal with
  | H : context [Z.shiftr ?x ?k] |- _ => rewrite (lxu_shiftr_div x k) in H by lia
  end;
  unfold zlow, zswrap in *;
  repeat match goal with
  | H : context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
  | H : context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b)
  | H : context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
  end;
  cbn [Z.b2z xorb andb orb negb] in *.

Ltac lxu_contra :=
  lxu_keep_arith; lxu_bvu_ranges; lxu_norm;
  first [ lia | (Z.div_mod_to_equations; lia) ].

Ltac lxu_chk_leaf fpc :=
  lazymatch goal with
  | |- context [MS _ _ (Z_to_bv 64 fpc) _ _ _ _] => exfalso; lxu_contra
  end.

Ltac lxu_chk_leaves fpc :=
  lazymatch goal with
  | |- context [MS _ _ (Z_to_bv 64 fpc) _ _ _ _] => lxu_chk_leaf fpc
  | |- _ => idtac
  end.

Lemma lxu_lor_align4 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> zlow 64 (Z.land (Z.lor a b) 3) = zlow 64 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ha, Hb. reflexivity.
Qed.

Ltac lxu_lor_align_leaf :=
  lazymatch goal with
  | H : (if zlow 64 (Z.land (Z.lor ?a ?b) 3) =? zlow 64 0 then false else true) = true |- False =>
      rewrite (lxu_lor_align4 a b) in H
        by (first [ (repeat match goal with H' : _ \/ _ |- _ => clear H' end); lia | lia ]);
      rewrite Z.eqb_refl in H; discriminate H
  end.

Ltac lxu_bvu_vars :=
  repeat match goal with
  | H : context [bv_unsigned ?w] |- _ => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (lxu_bvu_range w) end
  | |- context [bv_unsigned ?w] => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (lxu_bvu_range w) end
  end.

Ltac lxu_len_post :=
  repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end;
  match goal with HR : ?r = 0 -> _, HB : -127 < ?r <= 0 |- _ =>
    let a := fresh "HR" in let b := fresh "HR" in let rn := fresh "RN" in
    destruct (Z.eq_dec r 0) as [R0|R0];
    [ subst r; specialize (HR eq_refl); destruct HR as [a b]
    | assert (rn : r <= -1) by lia; clear HR R0 ] end.

Ltac lxu_pnull K :=
  exfalso;
  repeat match type of K with context [?a <? ?b] =>
    first [ let E := fresh "E" in assert (E : (a <? b) = true) by (apply Z.ltb_lt; lia); rewrite E in K; clear E
          | let E := fresh "E" in assert (E : (a <? b) = false) by (apply Z.ltb_ge; lia); rewrite E in K; clear E ] end;
  vm_compute in K; first [ discriminate K | lia ].

Ltac lxu_al_close K :=
  exfalso; rewrite ?unsigned_lit in K by lia;
  rewrite ?lxu_land1, ?lxu_land3, ?lxu_land7, ?lxu_land15 in K; lia.
