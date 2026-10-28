(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_f128_mul_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac zeq_fast ::=
  first
  [ reflexivity
  | lazymatch goal with
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq_fast
              | unfold1 a; unfold1 c; zeq_boolarith_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
              | unfold1 a; unfold1 c; zeq_boolarith_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq_fast | unfold1 a; unfold1 c; zeq_boolarith_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- negb _ = negb _ => f_equal; zeq_fast
    | |- @eq bool _ _ => zeq_boolarith_fast
    end
  | slim; lia ].

Lemma mulhu_range : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= Z.shiftr (x * y) 64 < 18446744073709551616.
Proof.
  intros x y Hx Hy. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; nia. }
  apply Z.div_lt_upper_bound; [lia|]. change 18446744073709551616 with (2^64). nia.
Qed.

Ltac name_mulhu n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 (Z.shiftr (?x * ?y) 64) =>
      set (X := Z.shiftr (x * y) 64);
      let RX := fresh "R" X in
      assert (RX : 0 <= X < 18446744073709551616)
        by (cbv delta [X]; apply mulhu_range; (change (inr64 x) || idtac); [change (inr64 x); zrange | change (inr64 y); zrange])
  end.

Lemma three_hi : forall bHi h, 0 <= bHi < 2^64 -> 0 <= h < 2^64 ->
  Z_to_bv 64 (bHi * 3 + h) = Z_to_bv 64 (Z.land (Z.land (h + bHi) 18446744073709551615 + Z.land (Z.shiftl bHi 1) 18446744073709551615) 18446744073709551615).
Proof. intros. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma three_lo : forall bLo, 0 <= bLo < 2^64 ->
  Z.land (bLo * 3) 18446744073709551615 = Z.land (Z.land (Z.shiftl bLo 1) 18446744073709551615 + bLo) 18446744073709551615.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma five_hi : forall bHi h, 0 <= bHi < 2^64 -> 0 <= h < 2^64 ->
  Z_to_bv 64 (bHi * 5 + h) = Z_to_bv 64 (Z.land (Z.land (h + bHi) 18446744073709551615 + Z.land (Z.shiftl bHi 2) 18446744073709551615) 18446744073709551615).
Proof. intros. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma five_lo : forall bLo, 0 <= bLo < 2^64 ->
  Z.land (bLo * 5) 18446744073709551615 = Z.land (Z.land (Z.shiftl bLo 2) 18446744073709551615 + bLo) 18446744073709551615.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.

Ltac subst_head_let :=
  lazymatch goal with
  | |- (let x := ?v in ?c) = ?r =>
      is_var v;
      let c' := eval cbv beta in ((fun x : Z => c) v) in
      change (c' = r)
  end.
Ltac fold_model_lets2 := repeat first [ fold_head_let | subst_head_let ].

Section DivRound.
  Variables (w0 w1 w2 w3 w4 w5 w6 : word).
  Notation sgn := (bv_unsigned w0). Notation aH := (bv_unsigned w1). Notation aL := (bv_unsigned w2).
  Notation rH := (bv_unsigned w3). Notation rL := (bv_unsigned w4). Notation bH := (bv_unsigned w5). Notation bL := (bv_unsigned w6).

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; reflexivity)
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

End DivRound.
