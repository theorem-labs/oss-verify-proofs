(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Lemma gw_code : CodeAt.code_at usegs 0xd2f24 (QVbl.Mq0.fe_getround_code 0xfff54597 0x0f058593).  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd2f24 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd2f24 /\ 0xd2f24 + 60 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition fe_getround_entry := 0xd2f24%Z.
Lemma gw_eq_fe_getround_entry : @fe_getround_entry = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_getround_entry 0xd2f24) (@fe_getround_entry)). Proof. unfold fe_getround_entry, QVbl.Mq0.fe_getround_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fe_getround_entry : gw_eqs.
Definition fe_raise_inexact_entry := 0xd2f54%Z.
Lemma gw_eq_fe_raise_inexact_entry : @fe_raise_inexact_entry = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_raise_inexact_entry 0xd2f24) (@fe_raise_inexact_entry)). Proof. unfold fe_raise_inexact_entry, QVbl.Mq0.fe_raise_inexact_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fe_raise_inexact_entry : gw_eqs.

Definition fe_getround_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.
Lemma gw_eq_fe_getround_post : @fe_getround_post = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_getround_post usegs) (@fe_getround_post)). Proof. unfold fe_getround_post, QVbl.Mq0.fe_getround_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fe_getround_post : gw_eqs.

Lemma fe_getround_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq0.fe_getround_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser) [[@gw_eq_fe_getround_post]; [@gw_eq_fe_getround_entry__3; @gw_eq_fe_getround_entry__2; @gw_eq_fe_getround_entry]; [@gw_eq_fe_raise_inexact_entry__3; @gw_eq_fe_raise_inexact_entry__2; @gw_eq_fe_raise_inexact_entry]] '([864036]%Z : list Z) '(Q6nq.gwt_unf (@fe_getround_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_fe_getround_post; first [GwInst.gw_exact (@QVbl.Mq0.fe_getround_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq0.fe_getround_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser)]. Qed.

Definition fe_raise_inexact_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists fc',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m /\ frm0 fc'.
Lemma gw_eq_fe_raise_inexact_post : @fe_raise_inexact_post = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_raise_inexact_post usegs) (@fe_raise_inexact_post)). Proof. unfold fe_raise_inexact_post, QVbl.Mq0.fe_raise_inexact_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fe_raise_inexact_post : gw_eqs.

Lemma fe_raise_inexact_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq0.fe_raise_inexact_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser) [[@gw_eq_fe_raise_inexact_post]; [@gw_eq_fe_getround_entry__3; @gw_eq_fe_getround_entry__2; @gw_eq_fe_getround_entry]; [@gw_eq_fe_raise_inexact_entry__3; @gw_eq_fe_raise_inexact_entry__2; @gw_eq_fe_raise_inexact_entry]; [@gw_eq_fe_getround_post__3; @gw_eq_fe_getround_post__2; @gw_eq_fe_getround_post]] '([864084]%Z : list Z) '(Q6nq.gwt_unf (@fe_raise_inexact_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_fe_raise_inexact_post; first [GwInst.gw_exact (@QVbl.Mq0.fe_raise_inexact_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq0.fe_raise_inexact_spec usegs 0xd2f24 0xfff54597 0x0f058593 gw_code gw_base4 gw_baser)]. Qed.
