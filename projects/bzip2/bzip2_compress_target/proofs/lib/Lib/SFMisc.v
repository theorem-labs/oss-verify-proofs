(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module Walk.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
Import ListNotations.
Local Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
End Walk.

Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.Walk.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)

Ltac bool_atom_cases :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
  end.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

(* [comment removed for export] *)
Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
  intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
  rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
  rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
  rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : forall x, (0 <= x)%Z ->
  Z.land (x + 1) 18446744073709551614 = ((x + x mod 2) mod 2^64)%Z.
Proof.
  intros x Hx. rewrite land_even_mask, land_W64, land_1.
  destruct (Z.eq_dec (x mod 2) 0) as [E|E].
  - rewrite E, Z.add_0_r.
    assert (H1 : ((x + 1) mod 2 = 1)%Z) by (rewrite Z.add_mod, E by lia; reflexivity).
    rewrite H1.
    destruct (Z_lt_le_dec ((x + 1) mod 2^64) 1) as [L|L].
    + exfalso. assert (HH : ((x+1) mod 2^64 = 0)%Z) by (pose proof (Z.mod_pos_bound (x+1) (2^64)); lia).
      apply Z.mod_divide in HH; [|lia]. destruct HH as [q Hq].
      assert (H2 : ((x + 1) mod 2 = 0)%Z). { rewrite Hq. replace (2^64)%Z with (2^63 * 2)%Z by reflexivity. rewrite Z.mul_assoc. apply Z.mod_mul. lia. } lia.
    + rewrite <- (Z.mod_small ((x + 1) mod 2 ^ 64 - 1) (2^64)) by (pose proof (Z.mod_pos_bound (x+1) (2^64)); lia).
      rewrite Zminus_mod_idemp_l. f_equal. lia.
  - assert (E1 : (x mod 2 = 1)%Z) by (pose proof (Z.mod_pos_bound x 2); lia). rewrite E1.
    assert (H1 : ((x + 1) mod 2 = 0)%Z) by (rewrite Z.add_mod, E1 by lia; reflexivity).
    rewrite H1. lia.
Qed.

(* [comment removed for export] *)
Ltac weq :=
  first [ reflexivity
        | f_equal; zeq
        | rewrite round_even_idiom by zrange_nonneg; weq_arith
        | weq_arith ]
with weq_arith :=
  apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
  bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
