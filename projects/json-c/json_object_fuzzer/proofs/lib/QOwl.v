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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnyT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4zb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4zb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdvg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdvg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x56dd4 QQLG.Mq0.addtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x56dd4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x56dd4 /\ 0x56dd4 + 1996 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Ltac reg_eq_ev := first [ reflexivity | (symmetry; apply Z_to_bv_bv_unsigned) | apply Z_to_bv_bv_unsigned ].
Ltac tree_eq_ev :=
first [ reflexivity
| lazymatch goal with
| |- TNode _ _ _ = TNode _ _ _ => f_equal; tree_eq_ev
| |- Some _ = Some _ => f_equal; reg_eq_ev
| |- _ => reg_eq_ev
end ].
Ltac ms_eq_ev :=
lazymatch goal with
| |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => unfold mkR; f_equal; [ tree_eq_ev | reflexivity .. ]
end.

Ltac jump L := eapply evt_eq; [ | eapply L ]; first [ ms_eq_ev | finL ].

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

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QDXD.Mq0.addtf3_post) (@QnyT.addtf3_post) (Q6nq.gwt_def (@QQLG.Mq0.addtf3_post) (@QnyT.addtf3_post) Q6nq.gwt_nil)).
Lemma add_LM1 : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_LM1 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355924]%Z : list Z) 'gwt_X).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_LM1 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_L108 : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_L108 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([356036]%Z : list Z) 'gwt_X).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_L108 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_L0f4 : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_L0f4 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([356016]%Z : list Z) 'gwt_X).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_L0f4 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_LS : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_LS rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355996]%Z : list Z) 'gwt_X).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_LS rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_L074 : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_L074 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355888; 9223653511831486464]%Z : list Z) '(Q6nq.gwt_unf (@SPEC_K) gwt_X)).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_L074 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.

Lemma add_L034 : ltac2:(Q6nq.tyx '(@QDXD.Mq0.add_L034 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355824]%Z : list Z) 'gwt_X).
Proof using FR FRM MI MU STK WM. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.add_L034 rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.
End Proofs.

Lemma addtf3_spec : ltac2:(Q6nq.tyx '(@QDXD.Mq0.addtf3_spec rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([355796]%Z : list Z) '(Q6nq.gwt_unf (@addtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.Mq0.addtf3_spec rsegs 0x56dd4 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec). Qed.
