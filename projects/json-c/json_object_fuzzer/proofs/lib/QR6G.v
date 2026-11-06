(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at usegs 0xd252c QQLG.Mqc.trunctfdf2_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd252c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd252c /\ 0xd252c + 488 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition trunctfdf2_entry := 0xd252c%Z.
Lemma gw_eq_trunctfdf2_entry : @trunctfdf2_entry = ltac:(GwInst.gw_term (@QQLG.Mqc.trunctfdf2_entry 0xd252c) (@trunctfdf2_entry)). Proof. unfold trunctfdf2_entry, QQLG.Mqc.trunctfdf2_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_trunctfdf2_entry : gw_eqs.

Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition trunctfdf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 r) F) (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
Lemma gw_eq_trunctfdf2_post : @trunctfdf2_post = ltac:(GwInst.gw_term (@QQLG.Mqc.trunctfdf2_post usegs) (@trunctfdf2_post)). Proof. unfold trunctfdf2_post, QQLG.Mqc.trunctfdf2_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_trunctfdf2_post : gw_eqs.

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 IMPLICIT_HI INF_HI HALF60 DQUIET].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv usegs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono usegs m m := wmono_refl usegs m.

Lemma trunc_Lpack : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_Lpack usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861672]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_Lpack usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_Lpack usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_LN : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_LN usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861656]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_LN usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_LN usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_L5 : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_L5 usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861952]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_L5 usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_L5 usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_L4 : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_L4 usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861880]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_L4 usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_L4 usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_L3 : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_L3 usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861824]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_L3 usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_L3 usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_L0c : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_L0c usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861620]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_L0c usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_L0c usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.

Lemma trunc_main : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunc_main usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]; [@gw_eq_trunctfdf2_post__3; @gw_eq_trunctfdf2_post__2; @gw_eq_trunctfdf2_post]] '([861484]%Z : list Z) '(Q6nq.gwt_unf (@trunctfdf2_entry) Q6nq.gwt_nil)).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QQLG.Mqc.trunc_main usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunc_main usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.
End Proofs.

Lemma trunctfdf2_spec : ltac2:(Q6nq.tyx '(@QQLG.Mqc.trunctfdf2_spec usegs 0xd252c gw_code gw_base4 gw_baser) [[@gw_eq_trunctfdf2_post]; [@gw_eq_trunctfdf2_entry__3; @gw_eq_trunctfdf2_entry__2; @gw_eq_trunctfdf2_entry]] '([861484]%Z : list Z) '(Q6nq.gwt_unf (@trunctfdf2_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_trunctfdf2_post; first [GwInst.gw_exact (@QQLG.Mqc.trunctfdf2_spec usegs 0xd252c gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mqc.trunctfdf2_spec usegs 0xd252c gw_code gw_base4 gw_baser)]. Qed.
