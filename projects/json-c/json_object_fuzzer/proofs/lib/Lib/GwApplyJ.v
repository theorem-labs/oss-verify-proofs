(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen GwApply GwApply2.
From Ltac2 Require Import Ltac2 Constr Control Message.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Set Default Proof Mode "Classic".

Definition gw_uses {A : Type} (_ : A) (P : Prop) : Prop := P.

Ltac gw_cs :=
lazymatch goal with
| |- ?P ?a =>
first [ match goal with H : (?A <= a < _)%Z, C : forall x, (?A <= x < _)%Z -> P x |- _ => apply C; lia end
| match goal with C : forall x, (_ <= x < _)%Z -> P x |- _ => apply C; lia end ]
end.

Lemma gw_ret_pc_var : forall (b n : Z), gw_b4 b -> gw_br b n -> (0 <= n)%Z -> ret_pc (Z_to_bv 64 b) = Z_to_bv 64 b.
Proof.
intros b n H4 HR Hn. pose proof (ret_pc_base b n 0 H4 HR) as X. replace (b + 0)%Z with b in X by (symmetry; apply Z.add_0_r).
apply X. apply andb_true_iff. split; [apply andb_true_iff; split|]; [reflexivity | reflexivity | apply Z.leb_le; exact Hn].
Qed.

Ltac gw_ret_pc_var_tac :=
lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?e)) _ _ _ _) =>
lazymatch goal with
| H4 : gw_b4 e, HR : gw_br e ?n |- _ =>
let X := fresh in
assert (X : ret_pc (Z_to_bv 64 e) = Z_to_bv 64 (e + 0)%Z)
by (rewrite (gw_ret_pc_var e n H4 HR) by (unfold gw_br in HR; lia); f_equal; lia);
rewrite X; clear X
| _ => fail "gw_ret_pc_var_tac: no gw_b4 / gw_br facts for the entry variable" e
end
| _ => idtac
end.

Ltac gwj_pc_norm :=
lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
first [ match goal with
| H4 : gw_b4 ?e, HR : gw_br ?e ?n |- _ =>
is_var e; unify x e;
let X := fresh in
assert (X : ret_pc (Z_to_bv 64 e) = Z_to_bv 64 (e + 0)%Z)
by (rewrite (gw_ret_pc_var e n H4 HR) by (unfold gw_br in HR; lia); f_equal; lia);
change (ret_pc (Z_to_bv 64 x)) with (ret_pc (Z_to_bv 64 e)); rewrite X; clear X
end
| idtac ]
| L : gw_anch _ (?e + 0)%Z |- evt _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) =>
tryif is_var e then replace (Z_to_bv 64 e) with (Z_to_bv 64 (e + 0)%Z) by (rewrite Z.add_0_r; reflexivity) else idtac
| _ => idtac
end.

Ltac gwj_expose_local :=
repeat match goal with
| H : gw_al _ _ |- _ => unfold gw_al in H
| H : gw_br _ _ |- _ => unfold gw_br in H
| H : gw_le _ _ |- _ => unfold gw_le in H
end.
Ltac gwj_align_solve A k :=
gwj_expose_local;
rewrite (unsigned_lit A) by lia;
lazymatch k with
| 3%Z => change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2)%Z with 4%Z
| 7%Z => change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3)%Z with 8%Z
| 1%Z => change 1%Z with (Z.ones 1); rewrite Z.land_ones by lia; change (2 ^ 1)%Z with 2%Z
end;
Z.div_mod_to_equations; lia.
Ltac gwj_align_norm :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ?A)) ?k)) (Z_to_bv 64 0)) then _ else _) _ _ _ _) =>
first [
(lazymatch A with
| (?g + ?d)%Z => is_var g; lazymatch goal with _ : gw_al g _ |- _ => idtac end
| ?g => is_var g; lazymatch goal with _ : gw_al g _ |- _ => idtac end
end);
let E := fresh in
assert (E : Z.land (bv_unsigned (Z_to_bv 64 A)) k = 0%Z) by (gwj_align_solve A k);
rewrite E; clear E;
change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false; cbv iota
| idtac ]
| _ => idtac
end.

Ltac gwj_close t :=
let ty := type of t in
let ty' := eval hnf in ty in
lazymatch ty' with
| forall x : ?A, _ =>
constr:(forall x : A, ltac:(let r := gwj_close constr:(t x) in exact r))
| _ => t
end.
Ltac2 gwj_callee_stmt0 (hdr : constr) (t : constr) (cb : constr) : constr :=
let names := List.append (gw_binder_names (Constr.type hdr)) [@segs; @base] in
gw2_callee_app names cb t (Constr.type t).
Ltac gw_callee_stmt2 hdr t cb :=
let f := ltac2:(hdr t cb |- let r := gwj_callee_stmt0 (Option.get (Ltac1.to_constr hdr)) (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr cb)) in
ltac1:(r |- let c := gwj_close r in exact c) (Ltac1.of_constr r)) in
f hdr t cb.
