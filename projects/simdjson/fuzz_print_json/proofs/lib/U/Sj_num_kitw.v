(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma lxor_sign_Z : forall x, (-9223372036854775808 <= x < 9223372036854775808)%Z ->
  Z.lxor (x mod 18446744073709551616) 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
  intros x Hx. change 9223372036854775808%Z with (2^63)%Z. change 18446744073709551616%Z with (2^64)%Z.
  rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia).
  change (2^63)%Z with 9223372036854775808%Z in *. change (2^64)%Z with 18446744073709551616%Z in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lxor_sign_Z0 : forall x, (0 <= x < 9223372036854775808)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof. intros x Hx. rewrite <- (Z.mod_small x 18446744073709551616) at 1 by lia. apply lxor_sign_Z. lia. Qed.

Ltac wnorm :=
  repeat match goal with
  | |- context [Z.lxor (?x mod 18446744073709551616) 9223372036854775808] => rewrite (lxor_sign_Z x) by lia
  | |- context [Z.lxor ?x 9223372036854775808] => num_simple_expr x; rewrite (lxor_sign_Z0 x) by lia
  end.
Ltac nnorm_w := nnorm_u; wnorm.

Ltac u_trap_b pc :=
  first [ exfalso;
          repeat match goal with
          | H : context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
          | H : context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
          end;
          cbn [Z.b2z] in *;
          repeat match goal with
          | H : context [Z.lxor ?a ?b] |- _ =>
              lazymatch a with 0%Z => idtac | 1%Z => idtac end; lazymatch b with 0%Z => idtac | 1%Z => idtac end;
              let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
          end;
          lia
        | fail 100 "TRAP reachable" pc ].

Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?P => change (hidden P) in H end.
Ltac reveal := repeat match goal with H : hidden _ |- _ => unfold hidden in H end.
