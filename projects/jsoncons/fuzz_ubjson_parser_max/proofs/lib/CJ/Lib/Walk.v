(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Export Tac Bytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Walk () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "2and"; "2eq"; "3Z"; "4add"; "4le"; "4lt"; "4ltb"; "4modulo"; "4pow"; "0x"; "0y"]]).
Lemma carry_sym : ltac2:(TCodec.tc2 tcn__CJ_Lib_Walk "N'3'1&5zr2%3221&6&9+2+R0%3221%5271%;271'2'0&7&8&4r4r3%3221+`PPPPPPPPPPP0%6221%8215%9225%<3;21p0>1p0?1pHL1pFM1").
Proof.
intros x y Hx Hy. change 18446744073709551616%Z with (2^64)%Z.
destruct (Z.lt_ge_cases (x + y) (2^64)).
- rewrite Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.
Lemma carry_sym' : ltac2:(TCodec.tc2 tcn__CJ_Lib_Walk "Q0'3'1&5zr2%3221&6&9+2+R0%3221%5271%;271'2'0&7&8&4r3r4%3221+`PPPPPPPPPPP0%6221%8214%7256%9214%;217%>3=41p0@1p0A1pHN1pFO1").
Proof. intros. rewrite Z.add_comm. reflexivity. Qed.
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
Lemma wrap64_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_Walk "='3'2&8r1&9+2+R0%3221%6251+`PPPPPPPPPPP0%8271%:3;31pF<1").
Proof. reflexivity. Qed.
Ltac name_virtual_tac X e :=
set (X := e);
let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
let RX := fresh "R" X in
first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
| idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
