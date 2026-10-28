(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q1jm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1jm.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Lemma gw_code : CodeAt.code_at rsegs 0x5f83c QQLG.Mq9.memmove_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5f83c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5f83c /\ 0x5f83c + 380 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition memmove_entry := 0x5f83c%Z.
Lemma gw_eq_memmove_entry : @memmove_entry = ltac:(GwInst.gw_term (@QQLG.Mq9.memmove_entry 0x5f83c) (@memmove_entry)). Proof. unfold memmove_entry, QQLG.Mq9.memmove_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memmove_entry : gw_eqs.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src].
Lemma gw_eq_memmove_post : @memmove_post = ltac:(GwInst.gw_term (@QQLG.Mq9.memmove_post rsegs) (@memmove_post)). Proof. unfold memmove_post, QQLG.Mq9.memmove_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memmove_post : gw_eqs.

Definition memmove_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at rsegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a2 < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5f83c) fc None m (seg_rom rsegs)).
Lemma gw_eq_memmove_stmt : @memmove_stmt = ltac:(GwInst.gw_term (@QQLG.Mq9.memmove_stmt rsegs 0x5f83c) (@memmove_stmt)). Proof. unfold memmove_stmt, QQLG.Mq9.memmove_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memmove_stmt : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQLG.Mq9.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QVbl.Mq3.memcpy_post) (@U4l4.memcpy_post) Q6nq.gwt_nil)).
Lemma bytes_at_same : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bytes_at_same rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bytes_at_same rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

Section NoOverlap.
Local Open Scope Z_scope.
#[using="Type"] Lemma mod_cases : forall x M, 0 < M -> - M <= x < 2 * M ->
x mod M = x \/ x mod M = x + M \/ x mod M = x - M.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.mod_cases rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="Type"] Lemma nooverlap_test : ltac2:(Q6nq.tyx '(@QQLG.Mq9.nooverlap_test rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '([18446744073709551616]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.nooverlap_test rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
End NoOverlap.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^63)%Z.

#[using="a0 a1 src LEN AB"] Lemma nlen : (0 <= n)%Z. Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.nlen rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN"] Lemma src_nth : ltac2:(Q6nq.tyx '(@QQLG.Mq9.src_nth rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.src_nth rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN"] Lemma fwd_read1 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fwd_read1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fwd_read1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN AB"] Lemma fwd_store1 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fwd_store1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fwd_store1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN"] Lemma fwd_read8 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fwd_read8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fwd_read8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN AB"] Lemma fwd_store8 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fwd_store8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fwd_store8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN"] Lemma bwd_read1 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bwd_read1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bwd_read1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN AB"] Lemma bwd_store1 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bwd_store1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bwd_store1 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN"] Lemma bwd_read8 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bwd_read8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bwd_read8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
#[using="LEN AB"] Lemma bwd_store8 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bwd_store8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bwd_store8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN"] Lemma ret_fwd : ltac2:(Q6nq.tyx '(@QQLG.Mq9.ret_fwd rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391368]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.ret_fwd rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN"] Lemma ret_bwd : ltac2:(Q6nq.tyx '(@QQLG.Mq9.ret_bwd rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391368]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.ret_bwd rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma fbl : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fbl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391284]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fbl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN"] Lemma src_win8 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.src_win8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.src_win8 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma fb : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fb rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391276]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fb rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma fwl : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fwl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391580]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fwl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma fw : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fw rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391568]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fw rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma fh : ltac2:(Q6nq.tyx '(@QQLG.Mq9.fh rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391388]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.fh rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="a2 src LEN"] Lemma negc_word : forall q, Z_to_bv 64 ((0 - q) mod 18446744073709551616) = Z_to_bv 64 (18446744073709551616 - q).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.negc_word rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bbl : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bbl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391344; 18446744073709551616]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bbl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bb2 : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bb2 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391324]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bb2 rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bb : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bb rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391320]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bb rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bwl : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bwl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391528]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bwl rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bw : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bw rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391508]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bw rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma bh : ltac2:(Q6nq.tyx '(@QQLG.Mq9.bh rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391468; 18446744073709551616]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.bh rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.

#[using="LEN AB"] Lemma memmove_body : ltac2:(Q6nq.tyx '(@QQLG.Mq9.memmove_body rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec) [[@gw_eq_memmove_entry__3; @gw_eq_memmove_entry__2; @gw_eq_memmove_entry]; [@gw_eq_memmove_post__3; @gw_eq_memmove_post__2; @gw_eq_memmove_post]; [@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391228]%Z : list Z) '(Q6nq.gwt_unf (@memmove_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.memmove_body rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
End Proofs.

Lemma memmove_spec : memmove_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq9.memmove_spec rsegs 0x5f83c gw_code gw_base4 gw_baser memcpy_spec). Qed.
