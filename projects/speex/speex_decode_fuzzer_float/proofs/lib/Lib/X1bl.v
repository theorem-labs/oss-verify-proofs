(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bx.
Local Open Scope Z_scope.

Class RunCeiling : Type := mkRunCeiling {
run_ceil : Z;
run_secret : word;
run_canary : word
}.

Definition alloc_ceiling_lo : Z := 0x7fff7f800000.
Definition alloc_ceiling_hi : Z := 0x7fffff800000.

Definition alloc_ceiling {RC : RunCeiling} : Z :=
Z.max 0x7fff7f800000 (Z.min 0x7fffff800000 run_ceil).
Arguments alloc_ceiling {RC} : simpl never.

Definition SECRET {RC : RunCeiling} : Z := bv_unsigned run_secret.
Arguments SECRET {RC} : simpl never.

Lemma alloc_ceiling_bounds {RC : RunCeiling} : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. unfold alloc_ceiling. lia. Qed.

Lemma alloc_ceiling_lt63 {RC : RunCeiling} : alloc_ceiling < 2^63.
Proof. unfold alloc_ceiling. lia. Qed.

Lemma alloc_ceiling_pos {RC : RunCeiling} : 0 < alloc_ceiling.
Proof. unfold alloc_ceiling. lia. Qed.

Lemma SECRET_range {RC : RunCeiling} : 0 <= SECRET < 2^64.
Proof. unfold SECRET. apply bv_unsigned_in_range. Qed.

Definition run_params (sp sec can : word) : RunCeiling :=
{| run_ceil := bv_unsigned sp - 0x800000 ; run_secret := sec ; run_canary := can |}.

Lemma alloc_ceiling_run_params : forall sp sec can,
0x7fff80000000 <= bv_unsigned sp <= 0x800000000000 ->
@alloc_ceiling (run_params sp sec can) = bv_unsigned sp - 0x800000.
Proof. intros sp sec can H. unfold alloc_ceiling, run_params, run_ceil. lia. Qed.

Lemma SECRET_run_params : forall sp sec can, @SECRET (run_params sp sec can) = bv_unsigned sec.
Proof. reflexivity. Qed.

Lemma run_secret_run_params : forall sp sec can, @run_secret (run_params sp sec can) = sec.
Proof. reflexivity. Qed.

Lemma run_canary_run_params : forall sp sec can, @run_canary (run_params sp sec can) = can.
Proof. reflexivity. Qed.

Lemma alloc_ceiling_window {RC : RunCeiling} : alloc_ceiling_lo <= alloc_ceiling <= alloc_ceiling_hi.
Proof. unfold alloc_ceiling_lo, alloc_ceiling_hi. apply alloc_ceiling_bounds. Qed.

Ltac2 rec ceil_arith (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ b => ceil_arith b
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
else if Constr.equal h '@Z.divide then true
else if Constr.equal h '@not then ceil_arith (Array.get args 0)
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h '@and then (if ceil_arith (Array.get args 0) then true else ceil_arith (Array.get args 1))
else if Constr.equal h '@or then (if ceil_arith (Array.get args 0) then true else ceil_arith (Array.get args 1))
else if Constr.equal h '@eq then (if Int.equal (Array.length args) 3 then Constr.equal (Array.get args 0) 'Z else false)
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
| _ => false
end.
Ltac2 ceil_unfold_locals () : unit :=
let r := [(reference:(alloc_ceiling), Std.AllOccurrences)] in
List.iter (fun h => let (id, body, ty) := h in
match body with
| Some _ => ()
| None =>
if ceil_arith ty then
Std.unfold r { Std.on_hyps := Some [(id, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences }
else ()
end) (Control.hyps ());
if ceil_arith (Control.goal ()) then
Std.unfold r { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
else ().
Ltac Zify.zify_pre_hook ::= ltac2:(Control.enter ceil_unfold_locals).
