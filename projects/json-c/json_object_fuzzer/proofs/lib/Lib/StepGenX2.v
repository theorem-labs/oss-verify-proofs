(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepFast. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import StepGen StepGenX StepGenSys.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
#[local] Set Default Proof Mode "Classic".
Open Scope bv_scope.

Ltac sg_guard :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ ?pcw _ _ _ _) =>
tryif is_var segs then
lazymatch pcw with
| Z_to_bv 64 (?b + ?k)%Z => idtac
| ret_pc _ => idtac
| (if _ then _ else _) => idtac
| _ => fail 0 "generic walk: the pc" pcw "is not in the engine's normal form Z_to_bv 64 (base + k) (abstract image: refusing to run the concrete engine)"
end
else idtac
| _ => idtac
end.
Ltac sg_step_core ::= sg_guard; ltac2:(sg_core false); try g_ret_pc. Ltac mkr__sg_step_core_0 := sg_guard; ltac2:(sg_core false); try g_ret_pc.
Ltac sg_zstep ::= sg_guard; ltac2:(sg_core true); try g_ret_pc. Ltac mkr__sg_zstep_1 := sg_guard; ltac2:(sg_core true); try g_ret_pc.

Ltac g_sys_nret_raw :=
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 (?b + ?k)%Z + Z_to_bv 64 4) _ _ _ _) =>
let k' := eval vm_compute in (k + 4)%Z in
rewrite (sg_pc_seq b k 4 k' eq_refl)
| _ => idtac
end);
first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].

Ltac g_ret_pc_any :=
repeat match goal with
| |- context [ret_pc (Z_to_bv 64 (?b + ?k)%Z)] =>
match goal with
| H4 : gw_b4 b, HR : gw_br b ?n |- _ => rewrite (ret_pc_base b n k H4 HR eq_refl)
end
end.
