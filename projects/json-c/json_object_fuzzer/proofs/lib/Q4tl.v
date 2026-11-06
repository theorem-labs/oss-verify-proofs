(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.

Module GwI.
Definition segs := usegs.
Definition base := 0xd2714%Z.
Lemma CODE : CodeAt.code_at usegs 0xd2714 QQLG.Mq5.fpclassifyl_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0xd2714 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0xd2714 /\ 0xd2714 + 68 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition fpclassifyl_entry := 0xd2714%Z.
Lemma gw_eq_fpclassifyl_entry : @fpclassifyl_entry = ltac:(GwInst.gw_term (@QQLG.Mq5.fpclassifyl_entry 0xd2714) (@fpclassifyl_entry)). Proof. unfold fpclassifyl_entry, QQLG.Mq5.fpclassifyl_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fpclassifyl_entry : gw_eqs.

Definition fpclassifyl_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.
Lemma gw_eq_fpclassifyl_post : @fpclassifyl_post = ltac:(GwInst.gw_term (@QQLG.Mq5.fpclassifyl_post usegs) (@fpclassifyl_post)). Proof. unfold fpclassifyl_post, QQLG.Mq5.fpclassifyl_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fpclassifyl_post : gw_eqs.

Lemma fpc_exp_field : ltac2:(Q6nq.tyx '(@QQLG.Mq5.fpc_exp_field) [[@gw_eq_fpclassifyl_entry__3; @gw_eq_fpclassifyl_entry__2; @gw_eq_fpclassifyl_entry]; [@gw_eq_fpclassifyl_post__3; @gw_eq_fpclassifyl_post__2; @gw_eq_fpclassifyl_post]] '([18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq5.fpc_exp_field). Qed.
Lemma fpc_mant_field : ltac2:(Q6nq.tyx '(@QQLG.Mq5.fpc_mant_field) [[@gw_eq_fpclassifyl_entry__3; @gw_eq_fpclassifyl_entry__2; @gw_eq_fpclassifyl_entry]; [@gw_eq_fpclassifyl_post__3; @gw_eq_fpclassifyl_post__2; @gw_eq_fpclassifyl_post]] '([18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq5.fpc_mant_field). Qed.

Lemma fpclassifyl_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq5.fpclassifyl_spec) [[@gw_eq_fpclassifyl_entry__3; @gw_eq_fpclassifyl_entry__2; @gw_eq_fpclassifyl_entry]; [@gw_eq_fpclassifyl_post__3; @gw_eq_fpclassifyl_post__2; @gw_eq_fpclassifyl_post]] '([861972]%Z : list Z) '(Q6nq.gwt_unf (@fpclassifyl_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq5.fpclassifyl_spec). Qed.
