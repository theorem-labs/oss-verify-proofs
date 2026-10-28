(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export BTac BBytes.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac zeq :=
  first
  [ reflexivity
  | lazymatch goal with

    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]

    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq

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

with unfold1 a := try (is_var a; cbv delta [a])

with zeq_boolarith :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

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

Ltac name_as_tac X e :=
  set (X := e);
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

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

Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
