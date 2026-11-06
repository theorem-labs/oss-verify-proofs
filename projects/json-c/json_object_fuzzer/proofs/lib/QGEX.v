(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWCD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWCD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnyT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnyT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOwl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOwl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x56dc4 QkTt.Mq1.subtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x56dc4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x56dc4 /\ 0x56dc4 + 16 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition subtf3_entry := 0x56dc4%Z.
Lemma gw_eq_subtf3_entry : @subtf3_entry = ltac:(GwInst.gw_term (@QkTt.Mq1.subtf3_entry 0x56dc4) (@subtf3_entry)). Proof. unfold subtf3_entry, QkTt.Mq1.subtf3_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_subtf3_entry : gw_eqs.

Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Mq1.land_shl64_low rsegs 0x56dc4 gw_code gw_base4 gw_baser addtf3_spec). Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QkTt.Mq1.addtf3_post) (@QnyT.addtf3_post) (Q6nq.gwt_def (@QQLG.Mq0.addtf3_post) (@QnyT.addtf3_post) Q6nq.gwt_nil)).
Lemma f128_sub_split : ltac2:(Q6nq.tyx '(@QkTt.Mq1.f128_sub_split rsegs 0x56dc4 gw_code gw_base4 gw_baser addtf3_spec) [[@gw_eq_subtf3_entry__3; @gw_eq_subtf3_entry__2; @gw_eq_subtf3_entry]] '([9223372036854775808]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Mq1.f128_sub_split rsegs 0x56dc4 gw_code gw_base4 gw_baser addtf3_spec). Qed.

Lemma subtf3_spec : ltac2:(Q6nq.tyx '(@QkTt.Mq1.subtf3_spec rsegs 0x56dc4 gw_code gw_base4 gw_baser addtf3_spec) [[@gw_eq_subtf3_entry__3; @gw_eq_subtf3_entry__2; @gw_eq_subtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355780]%Z : list Z) '(Q6nq.gwt_unf (@subtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Mq1.subtf3_spec rsegs 0x56dc4 gw_code gw_base4 gw_baser addtf3_spec). Qed.
