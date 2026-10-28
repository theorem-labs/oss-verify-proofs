(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x59328 (QVbl.Mq0.fe_getround_code 0xfffbd597 0x5ac58593).  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x59328 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x59328 /\ 0x59328 + 60 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition fe_getround_entry := 0x59328%Z.
Lemma gw_eq_fe_getround_entry : @fe_getround_entry = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_getround_entry 0x59328) (@fe_getround_entry)). Proof. unfold fe_getround_entry, QVbl.Mq0.fe_getround_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fe_getround_entry : gw_eqs.
Definition fe_raise_inexact_entry := 0x59358%Z.
Lemma gw_eq_fe_raise_inexact_entry : @fe_raise_inexact_entry = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_raise_inexact_entry 0x59328) (@fe_raise_inexact_entry)). Proof. unfold fe_raise_inexact_entry, QVbl.Mq0.fe_raise_inexact_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fe_raise_inexact_entry : gw_eqs.

Definition fe_getround_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_fe_getround_post : @fe_getround_post = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_getround_post rsegs) (@fe_getround_post)). Proof. unfold fe_getround_post, QVbl.Mq0.fe_getround_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fe_getround_post : gw_eqs.

Lemma fe_getround_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq0.fe_getround_spec rsegs 0x59328 0xfffbd597 0x5ac58593 gw_code gw_base4 gw_baser) [[@gw_eq_fe_getround_entry__3; @gw_eq_fe_getround_entry__2; @gw_eq_fe_getround_entry]; [@gw_eq_fe_raise_inexact_entry__3; @gw_eq_fe_raise_inexact_entry__2; @gw_eq_fe_raise_inexact_entry]; [@gw_eq_fe_getround_post__3; @gw_eq_fe_getround_post__2; @gw_eq_fe_getround_post]] '([365352]%Z : list Z) '(Q6nq.gwt_unf (@fe_getround_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq0.fe_getround_spec rsegs 0x59328 0xfffbd597 0x5ac58593 gw_code gw_base4 gw_baser). Qed.

Definition fe_raise_inexact_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists fc',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m /\ frm0 fc'.
Lemma gw_eq_fe_raise_inexact_post : @fe_raise_inexact_post = ltac:(GwInst.gw_term (@QVbl.Mq0.fe_raise_inexact_post rsegs) (@fe_raise_inexact_post)). Proof. unfold fe_raise_inexact_post, QVbl.Mq0.fe_raise_inexact_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fe_raise_inexact_post : gw_eqs.

Lemma fe_raise_inexact_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq0.fe_raise_inexact_spec rsegs 0x59328 0xfffbd597 0x5ac58593 gw_code gw_base4 gw_baser) [[@gw_eq_fe_getround_entry__3; @gw_eq_fe_getround_entry__2; @gw_eq_fe_getround_entry]; [@gw_eq_fe_raise_inexact_entry__3; @gw_eq_fe_raise_inexact_entry__2; @gw_eq_fe_raise_inexact_entry]; [@gw_eq_fe_getround_post__3; @gw_eq_fe_getround_post__2; @gw_eq_fe_getround_post]; [@gw_eq_fe_raise_inexact_post__3; @gw_eq_fe_raise_inexact_post__2; @gw_eq_fe_raise_inexact_post]] '([365400]%Z : list Z) '(Q6nq.gwt_unf (@fe_raise_inexact_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq0.fe_raise_inexact_spec rsegs 0x59328 0xfffbd597 0x5ac58593 gw_code gw_base4 gw_baser). Qed.
