(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.
Import ListNotations.
Open Scope Z_scope.

Lemma wz_neg_unsigned : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof. intros z. apply bv_eq. rewrite !unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616. rewrite Zminus_mod_idemp_r. f_equal. Qed.

Lemma ub_land7 : forall e, e mod 8 = 0 -> Z.land e 7 = 0.
Proof. intros e H. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. exact H. Qed.
Lemma ub_land3 : forall e, e mod 4 = 0 -> Z.land e 3 = 0.
Proof. intros e H. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. exact H. Qed.
Lemma ub_land1 : forall e, e mod 2 = 0 -> Z.land e 1 = 0.
Proof. intros e H. change 1 with (2^1 - 1). rewrite zb_land_mask by lia. exact H. Qed.
Ltac ub_mod_solve := repeat match goal with H : _ mod _ = 0 |- _ => revert H end; clear; intros; Z.div_mod_to_equations; lia.
Ltac ub_align_auto :=
repeat match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) _] => rewrite (unsigned_lit x) by lia end;
first [ match goal with |- context [Z.land ?e 7] => rewrite (ub_land7 e) by ub_mod_solve end
| match goal with |- context [Z.land ?e 3] => rewrite (ub_land3 e) by ub_mod_solve end
| match goal with |- context [Z.land ?e 1] => rewrite (ub_land1 e) by ub_mod_solve end ];
if_false.

Ltac ub_if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in
lazymatch v with true => idtac | false => idtac end;
change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac ub_cmp_norm :=
repeat first
[ match goal with |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
first [ rewrite (v_sltu_1' (Z_to_bv 64 x) (Z_to_bv 64 y)) by (rewrite (unsigned_lit x), (unsigned_lit y) by lia; lia)
| rewrite (v_sltu_0' (Z_to_bv 64 x) (Z_to_bv 64 y)) by (rewrite (unsigned_lit x), (unsigned_lit y) by lia; lia) ] end
| match goal with |- context [v_sltiu (Z_to_bv 64 ?x) ?imm] => rewrite (v_sltiu_0 (Z_to_bv 64 x) imm) by (rewrite ?(unsigned_lit x) by lia; lia) end
| match goal with |- context [v_slti (Z_to_bv 64 ?x) ?imm] => rewrite (v_slti_0 (Z_to_bv 64 x) imm) by (rewrite zsig_lit by lia; lia) end
| match goal with |- context [v_slt (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_slt_0 (Z_to_bv 64 x) (Z_to_bv 64 y)) by (rewrite !signed_lit by lia; lia) end
| match goal with |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?e)) ?k] =>
rewrite (unsigned_lit e) by lia; rewrite (Z.shiftr_div_pow2 e k) by lia; rewrite (Z.div_small e (2 ^ k)) by lia end ].

Ltac ub_cmp_auto :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
first [ replace c with false; [cbv iota | symmetry; ub_cmp_norm; timeout 10 (vm_compute; reflexivity)]   (* timeout-ok: on expiry this arm fails, and without this limit the build exceeds 250 GiB *)
| replace c with true; [cbv iota | symmetry; ub_cmp_norm; timeout 10 (vm_compute; reflexivity)] ]   (* timeout-ok: on expiry this arm fails, and without this limit the build exceeds 250 GiB *)
end.

Ltac ub_resolve :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
first [ timeout 5 ub_if_lit   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| match goal with H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] => ubsan_align H end
| match goal with H : ?p mod 16 = 0 |- context [Z.land ?p _] => ubsan_align H end
| ub_align_auto
| if_falsex
| ub_cmp_auto
| idtac ]
| |- _ => idtac
end.
Ltac ub_skip :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let b := eval vm_compute in (ub_ins pc) in
lazymatch b with
| true => step; ub_resolve; ub_skip
| _ => idtac
end
| |- _ => idtac
end.
Ltac bstep := ub_skip; step.
Ltac bstepz := ub_skip; stepz.
