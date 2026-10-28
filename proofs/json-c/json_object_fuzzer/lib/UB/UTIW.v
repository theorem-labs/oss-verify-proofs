(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5fe24%Z.
Definition w_8 := 0xcf8ff0ef%Z.
Definition joff_8 := (Z_to_bv 21 2094328).
Definition e_memchr := 0x5f33c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5fe24 (Q91D.Mq6.strnlen_code 0xcf8ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5fe24 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5fe24 /\ 0x5fe24 + 68 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memchr_spec := @memchr_spec.
End GwI.

Definition strnlen_entry := 0x5fe24%Z.
Lemma gw_eq_strnlen_entry : @strnlen_entry = ltac:(GwInst.gw_term (@Q91D.Mq6.strnlen_entry 0x5fe24) (@strnlen_entry)). Proof. unfold strnlen_entry, Q91D.Mq6.strnlen_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strnlen_entry : gw_eqs.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ bytes_at rsegs m' (bv_unsigned a0) buf.
Lemma gw_eq_strnlen_post : @strnlen_post = ltac:(GwInst.gw_term (@Q91D.Mq6.strnlen_post rsegs) (@strnlen_post)). Proof. unfold strnlen_post, Q91D.Mq6.strnlen_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strnlen_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q91D.Mq6.memchr_post) (@UzHs.memchr_post) (Q6nq.gwt_def (@QQLG.Mq8.memchr_post) (@UzHs.memchr_post) Q6nq.gwt_nil)).
Lemma strnlen_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq6.strnlen_spec) [[@gw_eq_strnlen_post]; [@gw_eq_strnlen_entry__3; @gw_eq_strnlen_entry__2; @gw_eq_strnlen_entry]] '([392740]%Z : list Z) '(Q6nq.gwt_unf (@strnlen_entry) gwt_X)).
Proof. rewrite ?gw_eq_strnlen_post; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq6.strnlen_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq6.strnlen_spec)]. Qed.
