(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWCD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWCD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UnyT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UnyT.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Lemma gw_code : CodeAt.code_at rsegs 0x58b5c QQLG.Mq0.addtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x58b5c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x58b5c /\ 0x58b5c + 1996 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
Hypothesis FRM : frm0 fc.
Hypothesis MI : mem_inv rsegs m1.
Hypothesis FR : rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk rsegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
Hypothesis WM : wmono rsegs m m1.
Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q91D.Mq0.addtf3_post) (@UnyT.addtf3_post) (Q6nq.gwt_def (@QQLG.Mq0.addtf3_post) (@UnyT.addtf3_post) Q6nq.gwt_nil)).
Lemma add_L658 : ltac2:(Q6nq.tyx '(@Q91D.Mq0.add_L658 rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([364956; 281474976710655; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) gwt_X))))).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq0.add_L658 rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_L488 : ltac2:(Q6nq.tyx '(@Q91D.Mq0.add_L488 rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([364492; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) gwt_X)).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq0.add_L488 rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_Lsub : ltac2:(Q6nq.tyx '(@Q91D.Mq0.add_Lsub rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([364424; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) gwt_X)).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq0.add_Lsub rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_Ladd : ltac2:(Q6nq.tyx '(@Q91D.Mq0.add_Ladd rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([364804; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) gwt_X)).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq0.add_Ladd rsegs 0x58b5c gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.
End Proofs.
