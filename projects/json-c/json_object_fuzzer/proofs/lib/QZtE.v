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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5627c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5627c QQLG.Mqa.signbitl_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5627c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5627c /\ 0x5627c + 8 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition signbitl_entry := 0x5627c%Z.
Lemma gw_eq_signbitl_entry : @signbitl_entry = ltac:(GwInst.gw_term (@QQLG.Mqa.signbitl_entry 0x5627c) (@signbitl_entry)). Proof. unfold signbitl_entry, QQLG.Mqa.signbitl_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_signbitl_entry : gw_eqs.

Definition signbitl_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_signbitl_post : @signbitl_post = ltac:(GwInst.gw_term (@QQLG.Mqa.signbitl_post rsegs) (@signbitl_post)). Proof. unfold signbitl_post, QQLG.Mqa.signbitl_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_signbitl_post : gw_eqs.

Lemma signbitl_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqa.signbitl_spec) [[@gw_eq_signbitl_entry__3; @gw_eq_signbitl_entry__2; @gw_eq_signbitl_entry]; [@gw_eq_signbitl_post__3; @gw_eq_signbitl_post__2; @gw_eq_signbitl_post]] '([352892]%Z : list Z) '(Q6nq.gwt_unf (@signbitl_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqa.signbitl_spec). Qed.
