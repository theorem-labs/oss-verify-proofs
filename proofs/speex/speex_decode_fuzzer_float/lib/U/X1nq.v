(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1cb X1c4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.

Lemma cells_bytes_f32 : forall ws, cells_bytes (f32 ws) = u32s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. rewrite f32_cons. cbn [cells_bytes cbytes u32s]. rewrite IH. reflexivity. Qed.

Lemma cells_wf_f32 : forall ws, cells_wf (f32 ws).
Proof. induction ws as [|w ws IH]; [exact I|]. rewrite f32_cons. cbn. split; [exact I| exact IH]. Qed.

Section WithSegs.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.

#[using="Type"] Lemma u32arr_of_f32 : forall m A ws, rw_cells segs m A (f32 ws) -> u32arr segs m A ws.
Proof.
intros m A ws [[Hwf Hb] Hw]. rewrite cells_bytes_f32 in Hb. rewrite cells_size_f32 in Hw. split; [exact Hb|].
replace (4 * Z.of_nat (length ws))%Z with (Z.of_nat (4 * length ws)) by lia. exact Hw.
Qed.

#[using="Type"] Lemma f32_of_u32arr : forall m A ws, u32arr segs m A ws -> rw_cells segs m A (f32 ws).
Proof.
intros m A ws [Hb Hw]. split; [split; [apply cells_wf_f32| rewrite cells_bytes_f32; exact Hb]|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw.
Qed.

#[using="Type"] Lemma u32arr_read_nth : forall m A ws (i : Z) a,
u32arr segs m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))).
Proof.
intros m A ws i a H Hi Ha. eapply u32arr_read; [exact H| apply nth_error_nth'; lia| lia| exact Ha].
Qed.
End WithSegs.

Lemma zbv_eqm : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). exact E.
Qed.
Lemma zbv_mod64 : forall x, Z_to_bv 64 (x mod 2^64) = Z_to_bv 64 x.
Proof. intros. apply zbv_eqm. apply Z.mod_mod. lia. Qed.
Lemma zbv_shl2_mod64 : forall x, Z_to_bv 64 (Z.shiftl (x mod 2^64) 2) = Z_to_bv 64 (x * 4).
Proof.
intros. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. apply zbv_eqm.
rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Lemma zbv_add_mod64_r : forall a b, Z_to_bv 64 (a + b mod 2^64) = Z_to_bv 64 (a + b).
Proof. intros. apply zbv_eqm. rewrite Z.add_mod_idemp_r by lia. reflexivity. Qed.
Lemma zbv_add_mod64_l : forall a b, Z_to_bv 64 (a mod 2^64 + b) = Z_to_bv 64 (a + b).
Proof. intros. apply zbv_eqm. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Lemma slti0_neg : forall v, - 9223372036854775808 <= v < 0 ->
(Z.lxor (v mod 18446744073709551616) 9223372036854775808 <? 9223372036854775808) = true.
Proof.
intros v Hv. change 9223372036854775808 with (2^63). change 18446744073709551616 with (2^64) in *.
replace (v mod 2^64) with (v + 2^64).
2:{ apply Z.mod_unique with (q := -1); [left; lia| lia]. }
rewrite zb_lxor_sign by lia.
replace ((v + 2 ^ 64 + 2 ^ 63) mod 2 ^ 64) with (v + 2^63).
2:{ apply Z.mod_unique with (q := 1); [left; lia| lia]. }
apply Z.ltb_lt. lia.
Qed.
Lemma slti0_nonneg : forall v, 0 <= v < 9223372036854775808 ->
(Z.lxor v 9223372036854775808 <? 9223372036854775808) = false.
Proof.
intros v Hv. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma slti0_nonneg_mod : forall v, 0 <= v < 9223372036854775808 ->
(Z.lxor (v mod 18446744073709551616) 9223372036854775808 <? 9223372036854775808) = false.
Proof. intros v Hv. rewrite Z.mod_small by lia. apply slti0_nonneg. exact Hv. Qed.

Lemma zbv_lnot : forall x, 0 <= x < 2^64 -> Z_to_bv 64 (Z.lnot x) = Z_to_bv 64 (18446744073709551615 - x).
Proof.
intros x Hx. apply zbv_eqm. unfold Z.lnot. change 18446744073709551615 with (2^64 - 1).
replace (Z.pred (- x)) with ((2^64 - 1 - x) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma length_upd_Z {X} : forall (l : list X) i x, Z.of_nat (length (upd l i x)) = Z.of_nat (length l).
Proof. intros. rewrite upd_length. reflexivity. Qed.

Ltac apart1_lia_with H := let K := fresh "AP" in pose proof H as K; unfold apart in K; lia.

Ltac apart1_lia :=
first
[ match goal with
| H : apart ?p _ ?q _ |- _ =>
lazymatch goal with |- context [p] => lazymatch goal with |- context [q] => idtac end end;
apart1_lia_with H
end
| match goal with
| H : apart ?p _ ?q _ |- _ =>
first [ lazymatch goal with |- context [p] => idtac end | lazymatch goal with |- context [q] => idtac end ];
apart1_lia_with H
end
| match goal with
| H : apart _ _ _ _ |- _ => apart1_lia_with H
end ].
Ltac alia := first [ lia | apart1_lia ].
Ltac aslia := first [ exact I | lia | apart1_lia | split; aslia ].
Ltac slia ::= aslia.
Ltac tlia ::= plia_gen ltac:(first [ tlia_stock | sf_unhide; apart1_lia ]).

Ltac decide_ltbs :=
repeat match goal with
| |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
end.
