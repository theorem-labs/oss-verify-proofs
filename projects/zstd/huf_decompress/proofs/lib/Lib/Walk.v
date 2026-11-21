(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (carry_sym, carry_sym', wrap64_lit)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export Tac Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Walk () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool>eq_true_iff_eqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses?iff_equivalenceI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8add_comm".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carry_sym : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x + y) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? y)%Z.
Proof.
  intros x y Hx Hy. change 18446744073709551616%Z with (2^64)%Z.
  destruct (Z.lt_ge_cases (x + y) (2^64)).
  - rewrite Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.
Lemma carry_sym' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((y + x) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? x)%Z.
Proof. intros. rewrite Z.add_comm. reflexivity. Qed.

(* [comment removed for export] *)
Ltac zeq :=
  first
  [ reflexivity
  | lazymatch goal with
    (* [comment removed for export] *)
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]
    (* [comment removed for export] *)
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq
    (* [comment removed for export] *)
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq | rewrite (Z.eqb_sym a b); f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- negb _ = negb _ => f_equal; zeq
    | |- @eq bool _ _ => zeq_boolarith
    end
  | lia ]
(* [comment removed for export] *)
with unfold1 a := try (is_var a; cbv delta [a])
(* [comment removed for export] *)
with zeq_boolarith :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac zeq_fast :=
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
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- negb _ = negb _ => f_equal; zeq_fast
    | |- @eq bool _ _ => zeq_boolarith_fast
    end
  | slim; lia ]
with zeq_boolarith_fast :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac getreg n :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

(* [comment removed for export] *)
Ltac name_as_tac X e :=
  set (X := e);
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

(* [comment removed for export] *)
Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

(* [comment removed for export] *)
Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wrap64_lit : forall x, (x mod 2^64 = x mod 18446744073709551616)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
