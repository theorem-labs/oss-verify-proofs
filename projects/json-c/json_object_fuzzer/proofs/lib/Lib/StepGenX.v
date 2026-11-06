(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepFast.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import StepGen.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
#[local] Set Default Proof Mode "Classic".
Open Scope bv_scope.

Ltac g_anchor_rw_one :=
match goal with
| |- context [(Z.shiftl (bv_signed ?hi) 12 + ?p + bv_signed ?lo)%Z] =>
match goal with H : gw_anch (Z.shiftl (bv_signed hi) 12 + p + bv_signed lo)%Z ?r |- _ =>
rewrite (H : (Z.shiftl (bv_signed hi) 12 + p + bv_signed lo)%Z = r) end
| |- context [(?b + ?k + bv_signed ?j)%Z] =>
match goal with H : gw_anch (b + k + bv_signed j)%Z ?r |- _ => rewrite (H : (b + k + bv_signed j)%Z = r) end
| |- context [(bv_unsigned (sx32 (Z_to_bv 64 ?jt)) + ?a)%Z] =>
match goal with H : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt)) + a)%Z ?r |- _ =>
rewrite (H : (bv_unsigned (sx32 (Z_to_bv 64 jt)) + a)%Z = r) end
| H : gw_anch ?l ?r |- _ =>
lazymatch l with
| (Z.shiftl (bv_signed _) 12 + _ + bv_signed _)%Z => fail
| (_ + _ + bv_signed _)%Z => fail
| (bv_unsigned (sx32 (Z_to_bv 64 _)) + _)%Z => fail
| _ => progress (rewrite (H : l = r))
end
end.
Ltac g_anchor_rw_any ::= repeat g_anchor_rw_one. Ltac mkr__g_anchor_rw_any_0 := repeat g_anchor_rw_one.
Ltac g_anchor_rw ::=
lazymatch goal with
| |- evt _ _ _ => repeat g_anchor_rw_one
| _ => idtac
end. Ltac mkr__g_anchor_rw_1 := lazymatch goal with
| |- evt _ _ _ => repeat g_anchor_rw_one
| _ => idtac
end.

Ltac g_amo_step AMO ::=
g_ret_pc;
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) =>
lazymatch goal with
| CODE : code_at segs base ?ws |- _ =>
let k := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_cbv; simp_regs; simp_is_x0; g_amo_align AMO; exec_cbv; simp_is_x0; g_amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end
end
end
end. Ltac mkr__g_amo_step_2 AMO := g_ret_pc;
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) =>
lazymatch goal with
| CODE : code_at segs base ?ws |- _ =>
let k := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_cbv; simp_regs; simp_is_x0; g_amo_align AMO; exec_cbv; simp_is_x0; g_amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end
end
end
end.

Ltac sg_step_core ::= ltac2:(sg_core false); try g_ret_pc. Ltac mkr__sg_step_core_3 := ltac2:(sg_core false); try g_ret_pc.
Ltac sg_zstep ::= ltac2:(sg_core true); try g_ret_pc. Ltac mkr__sg_zstep_4 := ltac2:(sg_core true); try g_ret_pc.
