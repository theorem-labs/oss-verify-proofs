(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUrT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkAv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkAv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmuX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmuX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at usegs 0xd1e2c QQLG.multf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd1e2c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd1e2c /\ 0xd1e2c + 1792 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q91D.multf3_post) (@QkAv.multf3_post) (Q6nq.gwt_def (@QCa8.multf3_post) (@QkAv.multf3_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma Lbchk : ltac2:(Q6nq.tyx '(@QCa8.Lbchk usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-600); (-80); 4096; 861216]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]]); first [GwInst.gw_exact (@QCa8.Lbchk usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lbchk usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.

#[using="Type"] Lemma Lp2r : ltac2:(Q6nq.tyx '(@QCa8.Lp2r usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 860680]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]]); first [GwInst.gw_exact (@QCa8.Lp2r usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lp2r usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.

#[using="Type"] Lemma Linfr : ltac2:(Q6nq.tyx '(@QCa8.Linfr usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 860340]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]]); first [GwInst.gw_exact (@QCa8.Linfr usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Linfr usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.

#[using="Type"] Lemma Lbr : ltac2:(Q6nq.tyx '(@QCa8.Lbr usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 860316; 9223372036854775807]%Z : list Z) '(Q6nq.gwt_unf (@ABS_HI) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]]); first [GwInst.gw_exact (@QCa8.Lbr usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lbr usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.

#[using="Type"] Lemma Lspec : ltac2:(Q6nq.tyx '(@QCa8.Lspec usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 860288]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]]); first [GwInst.gw_exact (@QCa8.Lspec usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Lspec usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.

#[using="Type"] Lemma multf3_walk : ltac2:(Q6nq.tyx '(@QCa8.multf3_walk usegs 0xd1e2c gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]] '([(-80); 4096; 859692]%Z : list Z) '(Q6nq.gwt_unf (@multf3_entry) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]]); first [GwInst.gw_exact (@QCa8.multf3_walk usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.multf3_walk usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.
End Walk.

Definition multf3_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk usegs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
mem_inv usegs m ->
(4096 <= bv_unsigned sp)%Z ->
evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_mul (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1e2c) fc None m (seg_rom usegs)).
Lemma gw_eq_multf3_stmt : @multf3_stmt = ltac:(GwInst.gw_term (@QCa8.multf3_stmt usegs 0xd1e2c) (@multf3_stmt)). Proof. unfold multf3_stmt, QCa8.multf3_stmt; ltac2:(GwEq.gw_rw [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_multf3_stmt : gw_eqs.

Theorem multf3_spec : multf3_stmt.
Proof. rewrite ?gw_eq_multf3_stmt; first [GwInst.gw_exact (@QCa8.multf3_spec usegs 0xd1e2c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.multf3_spec usegs 0xd1e2c gw_code gw_base4 gw_baser)]. Qed.
