(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Ltac2 Require Import Ltac2.
From Stdlib Require Import ZArith Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Definition otf_info (segs : list Segment) (pc : word) : Z * bool * option (instr * Z) :=
match fetch_word segs pc with
| Some w => (bv_unsigned w, is_ecall w, decode_any w)
| None => ((-1)%Z, false, None)
end.
Definition otf_eqdec_w : EqDecision (option (bv 32)). Proof. apply _. Defined.
Definition otf_eqdec_d : EqDecision (option (instr * Z)). Proof. apply _. Defined.
Definition otf_chkF (segs : list Segment) (pc w : Z) : bool :=
match fetch_word segs (Z_to_bv 64 pc) with Some x => Z.eqb (bv_unsigned x) w | None => false end.
Lemma otf_F_ok : forall segs pc (hp : BvWf 64 pc) w (hw : BvWf 32 w),
otf_chkF segs pc w = true -> fetch_word segs (@BV 64 pc hp) = Some (@BV 32 w hw).
Proof.
intros segs pc hp w hw H. unfold otf_chkF in H.
assert (E : @BV 64 pc hp = Z_to_bv 64 pc).
{ apply bv_eq. rewrite Z_to_bv_unsigned. simpl. symmetry. apply bv_wrap_small. apply bv_wf_in_range. exact hp. }
rewrite E. destruct (fetch_word segs (Z_to_bv 64 pc)) as [x|]; [|discriminate H].
apply Z.eqb_eq in H. f_equal. apply bv_eq. simpl. exact H.
Qed.
Definition otf_chkD (w : Z) (i : instr * Z) : bool := @bool_decide (decode_any (Z_to_bv 32 w) = Some i) (otf_eqdec_d _ _).
Lemma otf_D_ok : forall w (hw : BvWf 32 w) i, otf_chkD w i = true -> decode_any (@BV 32 w hw) = Some i.
Proof.
intros w hw i H. unfold otf_chkD in H. apply bool_decide_eq_true_1 in H.
assert (E : @BV 32 w hw = Z_to_bv 32 w).
{ apply bv_eq. rewrite Z_to_bv_unsigned. simpl. symmetry. apply bv_wrap_small. apply bv_wf_in_range. exact hw. }
rewrite E. exact H.
Qed.
Ltac2 otf_app (h : constr) (args : constr list) : constr := Constr.Unsafe.make (Constr.Unsafe.App h (Array.of_list args)).
Ltac2 otf_vmcast (c : constr) (t : constr) : constr := Constr.Unsafe.make (Constr.Unsafe.Cast c Constr.Cast.vm t).
Ltac2 otf_bv (n : constr) (z : constr) : constr := otf_app constr:(@BV) [n; z; constr:(I)].
Ltac2 rec otf_canon (c : constr) : constr :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App h args =>
if Bool.and (Constr.equal h constr:(@BV)) (Int.equal (Array.length args) 3)
then otf_bv (Array.get args 0) (Array.get args 1)
else otf_app h (List.map otf_canon (Array.to_list args))
| _ => c
end.
Ltac2 otf_decided (ty : constr) (dec : constr) (lhs : constr) (rhs : constr) : constr :=
let g := otf_app constr:(@eq) [ty; lhs; rhs] in
let d := otf_app dec [lhs; rhs] in
let chk := otf_app constr:(@eq) [constr:(bool); otf_app constr:(@bool_decide) [g; d]; constr:(true)] in
otf_app constr:(@bool_decide_eq_true_1) [g; d; otf_vmcast constr:(@eq_refl bool true) chk].
Ltac2 otf_fail (m : string) : 'a := Control.zero (Tactic_failure (Some (Message.of_string m))).
Ltac2 otf_term (kind : int) (segs : constr) (pcz : constr) : constr :=
let pcw := otf_bv constr:(64%N) pcz in
let info := Std.eval_vm None (otf_app constr:(otf_info) [segs; pcw]) in
let (wz, ev, od) := lazy_match! info with (?wz, ?ev, ?od) => (wz, ev, od) end in
(if Constr.equal wz constr:((-1)%Z) then otf_fail "otf: no code at this pc" else ());
let w := otf_bv constr:(32%N) wz in
let okv (chk : constr) := otf_vmcast constr:(@eq_refl bool true) (otf_app constr:(@eq) [constr:(bool); chk; constr:(true)]) in
if Int.equal kind 0 then
otf_app constr:(otf_F_ok) [segs; pcz; constr:(I); wz; constr:(I); okv (otf_app constr:(otf_chkF) [segs; pcz; wz])]
else if Int.equal kind 1 then
(match Constr.Unsafe.kind od with
| Constr.Unsafe.App h args =>
if Bool.and (Constr.equal h constr:(@Some)) (Int.equal (Array.length args) 2)
then let i := otf_canon (Array.get args 1) in
otf_app constr:(otf_D_ok) [wz; constr:(I); i; okv (otf_app constr:(otf_chkD) [wz; i])]
else otf_fail "otf: undecodable word"
| _ => otf_fail "otf: undecodable word"
end)
else
Constr.Unsafe.make (Constr.Unsafe.Cast (otf_app constr:(@eq_refl) [constr:(bool); ev]) Constr.Cast.default
(otf_app constr:(@eq) [constr:(bool); otf_app constr:(is_ecall) [w]; ev])).
Ltac2 otf_exact (kind : int) (segs : Ltac1.t) (pc : Ltac1.t) : unit :=
let s := Option.get (Ltac1.to_constr segs) in let p := Option.get (Ltac1.to_constr pc) in
let t := otf_term kind s p in exact $t.
Set Default Proof Mode "Classic".
Ltac oF segs pc := let f := ltac2:(s p |- otf_exact 0 s p) in f segs pc.
Ltac oD segs pc := let f := ltac2:(s p |- otf_exact 1 s p) in f segs pc.
Ltac oE segs pc := let f := ltac2:(s p |- otf_exact 2 s p) in f segs pc.
Ltac2 otf_word (segs : constr) (pcz : constr) : constr :=
let pcw := otf_bv constr:(64%N) pcz in
let info := Std.eval_vm None (otf_app constr:(otf_info) [segs; pcw]) in
let (wz, _, _) := lazy_match! info with (?wz, ?ev, ?od) => (wz, ev, od) end in
(if Constr.equal wz constr:((-1)%Z) then otf_fail "otf: no code at this pc" else ());
otf_bv constr:(32%N) wz.
Ltac oW segs pc := let f := ltac2:(s p |- let t := otf_word (Option.get (Ltac1.to_constr s)) (Option.get (Ltac1.to_constr p)) in exact $t) in f segs pc.
