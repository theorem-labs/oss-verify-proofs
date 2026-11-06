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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import StepGen.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac g_norm_pc :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 (?b + ?k1 + ?k2)%Z) _ _ _ _) =>
let k := eval vm_compute in (k1 + k2)%Z in
replace (b + k1 + k2)%Z with (b + k)%Z by (rewrite <- Z.add_assoc; reflexivity)
| _ => idtac
end.
Ltac g_step_core_fast segs R F base off fc rv m ro :=
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
tryif QZAa.alu_only i then
(eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_cbv; simp_is_x0; simp_regs; vnorm_rw_for i; QZAa.vnorm_tail_fast;
reflexivity
| g_norm_pc ])
else step_core segs R F (base + off)%Z fc rv m ro
| _ => step_core segs R F (base + off)%Z fc rv m ro
end
| _ => fail "generic: no code word at offset" off
end
| _ => fail "generic: no code_at hypothesis"
end.
Ltac g_step_fast :=
g_ret_pc;
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) => g_step_core_fast segs R F base off fc rv m ro
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "generic: pc is not base + offset:" pc
end.

