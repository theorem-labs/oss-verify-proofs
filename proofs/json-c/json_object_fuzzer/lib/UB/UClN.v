(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5fdc4%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5fdc4 Q91D.Mq5.strncmp_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5fdc4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5fdc4 /\ 0x5fdc4 + 96 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition strncmp_entry := 0x5fdc4%Z.
Lemma gw_eq_strncmp_entry : @strncmp_entry = ltac:(GwInst.gw_term (@Q91D.Mq5.strncmp_entry 0x5fdc4) (@strncmp_entry)). Proof. unfold strncmp_entry, Q91D.Mq5.strncmp_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strncmp_entry : gw_eqs.

Definition strncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (ls rs : list byte) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.
Lemma gw_eq_strncmp_post : @strncmp_post = ltac:(GwInst.gw_term (@Q91D.Mq5.strncmp_post rsegs) (@strncmp_post)). Proof. unfold strncmp_post, Q91D.Mq5.strncmp_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strncmp_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
Hypothesis MI : mem_inv rsegs m.
Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) ls.
Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) rs.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Notation A := (bv_unsigned a0).
Notation B := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Notation POST := (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).

Notation ST pc x10 x11 x12 x13 x14 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

#[using="m LS RS"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.bounds) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.bounds)]. Qed.

#[using="Type"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.byte_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.byte_range)]. Qed.

#[using="Type"] Lemma walk_at : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq5.walk_at) [[@gw_eq_strncmp_entry__3; @gw_eq_strncmp_entry__2; @gw_eq_strncmp_entry]; [@gw_eq_strncmp_post__3; @gw_eq_strncmp_post__2; @gw_eq_strncmp_post]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.walk_at) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.walk_at)]. Qed.

#[using="MI LS RS MU WM"] Lemma strncmp_ret : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq5.strncmp_ret) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_strncmp_entry__3; @gw_eq_strncmp_entry__2; @gw_eq_strncmp_entry]; [@gw_eq_strncmp_post__3; @gw_eq_strncmp_post__2; @gw_eq_strncmp_post]] '([392704]%Z : list Z) 'Q6nq.gwt_nil).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_ret) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_ret)]. Qed.

#[using="MI LS RS MU WM"] Lemma strncmp_loop : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq5.strncmp_loop) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_strncmp_entry__3; @gw_eq_strncmp_entry__2; @gw_eq_strncmp_entry]; [@gw_eq_strncmp_post__3; @gw_eq_strncmp_post__2; @gw_eq_strncmp_post]] '([392664]%Z : list Z) 'Q6nq.gwt_nil).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_loop) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_loop)]. Qed.

#[using="MI LS RS MU WM"] Lemma strncmp_body :
strncmp_model ls rs n = Some v ->
evt rsegs POST (ST 0x5fdc4 a0 a1 a2 a3 a4).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_body) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_body)]. Qed.
End Proofs.

Lemma strncmp_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq5.strncmp_spec) [[@gw_eq_strncmp_post]; [@gw_eq_strncmp_entry__3; @gw_eq_strncmp_entry__2; @gw_eq_strncmp_entry]] '([392644]%Z : list Z) '(Q6nq.gwt_unf (@strncmp_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_strncmp_post; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq5.strncmp_spec)]. Qed.
