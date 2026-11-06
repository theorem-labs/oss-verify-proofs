(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_sf_helpers.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_mul_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Lemma mulhu_range : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= Z.shiftr (x * y) 64 < 18446744073709551616.
Proof.
  intros x y Hx Hy. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; nia. }
  apply Z.div_lt_upper_bound; [lia|]. change 18446744073709551616 with (2^64). nia.
Qed.

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

End DivRound.
