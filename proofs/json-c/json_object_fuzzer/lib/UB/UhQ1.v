(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Lemma gw_code : CodeAt.code_at rsegs 0x582ac QQLG.multf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x582ac mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x582ac /\ 0x582ac + 1792 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition multf3_entry := 0x582ac%Z.
Lemma gw_eq_multf3_entry : @multf3_entry = ltac:(GwInst.gw_term (@QQLG.multf3_entry 0x582ac) (@multf3_entry)). Proof. unfold multf3_entry, QQLG.multf3_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_entry : gw_eqs.
Definition multf3_core_pc := 0x5832c%Z.
Lemma gw_eq_multf3_core_pc : @multf3_core_pc = ltac:(GwInst.gw_term (@QQLG.multf3_core_pc 0x582ac) (@multf3_core_pc)). Proof. unfold multf3_core_pc, QQLG.multf3_core_pc; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_core_pc : gw_eqs.
Definition multf3_mid_pc := 0x584b8%Z.
Lemma gw_eq_multf3_mid_pc : @multf3_mid_pc = ltac:(GwInst.gw_term (@QQLG.multf3_mid_pc 0x582ac) (@multf3_mid_pc)). Proof. unfold multf3_mid_pc, QQLG.multf3_mid_pc; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_mid_pc : gw_eqs.

Lemma mulhu_shl32 : ltac2:(Q6nq.tyx '(@QQLG.mulhu_shl32 rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_entry__3; @gw_eq_multf3_entry__2; @gw_eq_multf3_entry]; [@gw_eq_multf3_core_pc__3; @gw_eq_multf3_core_pc__2; @gw_eq_multf3_core_pc]; [@gw_eq_multf3_mid_pc__3; @gw_eq_multf3_mid_pc__2; @gw_eq_multf3_mid_pc]] '([4294967295; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@M32) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.mulhu_shl32 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Definition multf3_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(aExp bExp aSigHi aSigLo bSigHi bSigLo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists es hh hl lh ll y5' t1 t2' x8 x9 a5' a6' s2' s3' s4' s5' s6' s7' s8' t3 t4 t5 t6,
(forall signHi scale, mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale = MC_tail signHi es hh hl lh ll scale)
/\ (0 <= es < 65536)%Z /\ (0 <= hh < 2^64)%Z /\ (0 <= hl < 2^64)%Z /\ (0 <= lh < 2^64)%Z /\ (0 <= ll < 2^64)%Z /\
y5' = Z_to_bv 64 es /\ a5' = Z_to_bv 64 18446744073709551615 /\ a6' = Z_to_bv 64 281474976710655 /\ t2' = Z_to_bv 64 (-16383) /\
ms' = MS (mkR ra sp gp tp y5' t1 t2' x8 x9
a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh) a5' a6' (Z_to_bv 64 hl)
s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x584b8) fc None m (seg_rom rsegs).
Lemma gw_eq_multf3_mid : @multf3_mid = ltac:(GwInst.gw_term (@QQLG.multf3_mid rsegs 0x582ac) (@multf3_mid)). Proof. unfold multf3_mid, QQLG.multf3_mid; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_mid : gw_eqs.

Lemma multf3_core1 : ltac2:(Q6nq.tyx '(@QQLG.multf3_core1 rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_entry__3; @gw_eq_multf3_entry__2; @gw_eq_multf3_entry]; [@gw_eq_multf3_core_pc__3; @gw_eq_multf3_core_pc__2; @gw_eq_multf3_core_pc]; [@gw_eq_multf3_mid_pc__3; @gw_eq_multf3_mid_pc__2; @gw_eq_multf3_mid_pc]; [@gw_eq_multf3_mid__3; @gw_eq_multf3_mid__2; @gw_eq_multf3_mid]] '([32768; 361260; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) (Q6nq.gwt_unf (@multf3_core_pc) Q6nq.gwt_nil))))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.multf3_core1 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
