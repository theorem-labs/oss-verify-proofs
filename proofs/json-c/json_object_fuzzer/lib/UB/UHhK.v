(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.

Module GwI.
Definition segs := rsegs.
Definition base := 0x593f8%Z.
Lemma CODE : CodeAt.code_at rsegs 0x593f8 QQLG.Mq4.floatunsitf_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x593f8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x593f8 /\ 0x593f8 + 236 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition floatunsitf_entry := 0x593f8%Z.
Lemma gw_eq_floatunsitf_entry : @floatunsitf_entry = ltac:(GwInst.gw_term (@QQLG.Mq4.floatunsitf_entry 0x593f8) (@floatunsitf_entry)). Proof. unfold floatunsitf_entry, QQLG.Mq4.floatunsitf_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_floatunsitf_entry : gw_eqs.

Definition floatunsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_floatunsitf_post : @floatunsitf_post = ltac:(GwInst.gw_term (@QQLG.Mq4.floatunsitf_post rsegs) (@floatunsitf_post)). Proof. unfold floatunsitf_post, QQLG.Mq4.floatunsitf_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_floatunsitf_post : gw_eqs.

Lemma floatunsitf_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq4.floatunsitf_spec) [[@gw_eq_floatunsitf_entry__3; @gw_eq_floatunsitf_entry__2; @gw_eq_floatunsitf_entry]; [@gw_eq_floatunsitf_post__3; @gw_eq_floatunsitf_post__2; @gw_eq_floatunsitf_post]] '([365560]%Z : list Z) '(Q6nq.gwt_unf (@floatunsitf_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq4.floatunsitf_spec). Qed.
