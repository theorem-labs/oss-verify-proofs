(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification.
Lemma gw_code : CodeAt.code_at rsegs 0x5958c QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5958c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5958c /\ 0x5958c + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition divtf3_entry := 0x5958c%Z.
Lemma gw_eq_divtf3_entry : @divtf3_entry = ltac:(GwInst.gw_term (@QVbl.divtf3_entry 0x5958c) (@divtf3_entry)). Proof. unfold divtf3_entry, QVbl.divtf3_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_entry : gw_eqs.

Definition divtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 112) (bv_unsigned sp).
Lemma gw_eq_divtf3_post : @divtf3_post = ltac:(GwInst.gw_term (@QVbl.divtf3_post rsegs) (@divtf3_post)). Proof. unfold divtf3_post, QVbl.divtf3_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_post : gw_eqs.

Definition divtf3_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
mem_inv rsegs m ->
(4096 <= bv_unsigned sp)%Z ->
evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_div (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5958c) fc None m (seg_rom rsegs)).
Lemma gw_eq_divtf3_stmt : @divtf3_stmt = ltac:(GwInst.gw_term (@QVbl.divtf3_stmt rsegs 0x5958c) (@divtf3_stmt)). Proof. unfold divtf3_stmt, QVbl.divtf3_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_stmt : gw_eqs.
