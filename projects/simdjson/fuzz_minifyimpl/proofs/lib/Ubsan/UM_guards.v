(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma ubg_land_ones : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.
(* [comment removed for export] *)
Lemma ubg_land_7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). apply Z.land_ones. lia. Qed.
Ltac ubalign K := rewrite ?ubg_land_7 in K; Z.div_mod_to_equations.

Lemma b2z_lxor : forall b1 b2, Z.lxor (Z.b2z b1) (Z.b2z b2) = Z.b2z (xorb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2z_lor : forall b1 b2, Z.lor (Z.b2z b1) (Z.b2z b2) = Z.b2z (orb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2z_land : forall b1 b2, Z.land (Z.b2z b1) (Z.b2z b2) = Z.b2z (andb b1 b2).
Proof. intros [|] [|]; reflexivity. Qed.

(* [comment removed for export] *)
Ltac ubg_has_var c := match c with context [?v] => is_var v end.
Ltac ubg_closed t := tryif ubg_has_var t then fail else idtac.
(* [comment removed for export] *)
Ltac ubg_eval K :=
  repeat match type of K with
  | context [Z.lxor ?x ?y] => ubg_closed x; ubg_closed y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v in K
  | context [Z.land ?x ?y] => ubg_closed x; ubg_closed y; let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v in K
  | context [Z.lor ?x ?y] => ubg_closed x; ubg_closed y; let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v in K
  | context [Z.add ?x ?y] => ubg_closed x; ubg_closed y;
      lazymatch x with Z0 => fail | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let v := eval vm_compute in (Z.add x y) in change (Z.add x y) with v in K
  | context [Z.add Z0 ?y] => ubg_closed y; lazymatch y with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let v := eval vm_compute in (Z.add Z0 y) in change (Z.add Z0 y) with v in K
  end.

(* [comment removed for export] *)
Lemma ubg_lxor_sign : forall x, 0 <= x < 2^64 -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808) mod 18446744073709551616.
Proof. intros x Hx. change 9223372036854775808 with (2^63). change 18446744073709551616 with (2^64). apply zb_lxor_sign. exact Hx. Qed.

Ltac ubnorm K :=
  rewrite ?b2z_lxor, ?b2z_lor, ?b2z_land in K;
  rewrite ?zb_lxor_ones in K by lia; rewrite ?ubg_lxor_sign in K by lia; rewrite ?ubg_land_ones in K.
Ltac ubcases K :=
  repeat (match type of K with
          | context [Z.ltb ?x ?y] => revert K; destruct (Z.ltb_spec0 x y); intros K
          | context [Z.leb ?x ?y] => revert K; destruct (Z.leb_spec0 x y); intros K
          | context [Z.eqb ?x ?y] => revert K; destruct (Z.eqb_spec x y); intros K
          end);
  cbn [xorb orb andb negb Z.b2z] in K; ubg_eval K.
(* [comment removed for export] *)
Ltac ubguard K := ubnorm K; ubcases K; Z.div_mod_to_equations.
Ltac ubdec K := ubguard K.
