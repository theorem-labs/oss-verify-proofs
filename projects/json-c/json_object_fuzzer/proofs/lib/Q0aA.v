(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRsj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at usegs 0xd2758 QQLG.Mq0.addtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd2758 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd2758 /\ 0xd2758 + 1996 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition addtf3_entry := 0xd2758%Z.
Lemma gw_eq_addtf3_entry : @addtf3_entry = ltac:(GwInst.gw_term (@QQLG.Mq0.addtf3_entry 0xd2758) (@addtf3_entry)). Proof. unfold addtf3_entry, QQLG.Mq0.addtf3_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_addtf3_entry : gw_eqs.

Definition addtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ frm0 fc'
/\ stk usegs m' (bv_unsigned sp - 48) (bv_unsigned sp).
Lemma gw_eq_addtf3_post : @addtf3_post = ltac:(GwInst.gw_term (@QQLG.Mq0.addtf3_post usegs) (@addtf3_post)). Proof. unfold addtf3_post, QQLG.Mq0.addtf3_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_addtf3_post : gw_eqs.

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "t3=" x28; idtac "t4=" x29.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
Hypothesis FRM : frm0 fc.
Hypothesis MI : mem_inv usegs m1.
Hypothesis FR : rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk usegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
Hypothesis WM : wmono usegs m m1.
Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

Lemma add_Lret : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_Lret usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863964]%Z : list Z) 'Q6nq.gwt_nil).
Proof using FR MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_Lret usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_Lret usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.

Lemma add_Lround : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_Lround usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863824; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)).
Proof using FR FRM MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_Lround usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_Lround usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.

Lemma add_L704 : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_L704 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863812; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)).
Proof using FR FRM MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_L704 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_L704 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.

Lemma add_L6c0 : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_L6c0 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863744; 281474976710655; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil))))).
Proof using FR FRM MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_L6c0 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_L6c0 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.

Lemma add_LM8 : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_LM8 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863676; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)).
Proof using FR FRM MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_LM8 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_LM8 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.

Lemma add_LM7 : ltac2:(Q6nq.tyx '(@QQLG.Mq0.add_LM7 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_addtf3_entry__3; @gw_eq_addtf3_entry__2; @gw_eq_addtf3_entry]; [@gw_eq_addtf3_post__3; @gw_eq_addtf3_post__2; @gw_eq_addtf3_post]] '([863540; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)).
Proof using FR FRM MI MU STK WM. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mq0.add_LM7 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq0.add_LM7 usegs 0xd2758 gw_code gw_base4 gw_baser fe_getround_spec fe_raise_inexact_spec)]. Qed.
End Proofs.
