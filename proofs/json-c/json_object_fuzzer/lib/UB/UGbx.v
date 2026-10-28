(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujxo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujxo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x582ac QQLG.multf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x582ac mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x582ac /\ 0x582ac + 1792 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q91D.multf3_post) (@Uwbh.multf3_post) (Q6nq.gwt_def (@QCa8.multf3_post) (@Uwbh.multf3_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma Lbchk : ltac2:(Q6nq.tyx '(@QCa8.Lbchk rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-600); (-80); 4096; 362656]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lbchk rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lp2r : ltac2:(Q6nq.tyx '(@QCa8.Lp2r rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 362120]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lp2r rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Linfr : ltac2:(Q6nq.tyx '(@QCa8.Linfr rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361780]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Linfr rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lbr : ltac2:(Q6nq.tyx '(@QCa8.Lbr rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361756; 9223372036854775807]%Z : list Z) '(Q6nq.gwt_unf (@ABS_HI) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lbr rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lspec : ltac2:(Q6nq.tyx '(@QCa8.Lspec rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361728]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lspec rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma multf3_walk : ltac2:(Q6nq.tyx '(@QCa8.multf3_walk rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]] '([(-80); 4096; 361132]%Z : list Z) '(Q6nq.gwt_unf (@multf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.multf3_walk rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
End Walk.

Definition multf3_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk rsegs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
mem_inv rsegs m ->
(4096 <= bv_unsigned sp)%Z ->
evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_mul (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x582ac) fc None m (seg_rom rsegs)).
Lemma gw_eq_multf3_stmt : @multf3_stmt = ltac:(GwInst.gw_term (@QCa8.multf3_stmt rsegs 0x582ac) (@multf3_stmt)). Proof. unfold multf3_stmt, QCa8.multf3_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_stmt : gw_eqs.

Theorem multf3_spec : multf3_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.multf3_spec rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
