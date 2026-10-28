(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Lemma gw_code : CodeAt.code_at rsegs 0x5fbcc QVbl.Mq5.strcmp_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5fbcc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5fbcc /\ 0x5fbcc + 56 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition strcmp_entry := 0x5fbcc%Z.
Lemma gw_eq_strcmp_entry : @strcmp_entry = ltac:(GwInst.gw_term (@QVbl.Mq5.strcmp_entry 0x5fbcc) (@strcmp_entry)). Proof. unfold strcmp_entry, QVbl.Mq5.strcmp_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strcmp_entry : gw_eqs.

Definition strcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (ls rs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0' = Z_to_bv 64 (strcmp_model ls rs)
/\ bytes_at rsegs m' (bv_unsigned a0) (ls ++ [b0]) /\ bytes_at rsegs m' (bv_unsigned a1) (rs ++ [b0]).
Lemma gw_eq_strcmp_post : @strcmp_post = ltac:(GwInst.gw_term (@QVbl.Mq5.strcmp_post rsegs) (@strcmp_post)). Proof. unfold strcmp_post, QVbl.Mq5.strcmp_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strcmp_post : gw_eqs.

Definition strcmp_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte),
bytes_at rsegs m (bv_unsigned a0) (ls ++ [b0]) ->
bytes_at rsegs m (bv_unsigned a1) (rs ++ [b0]) ->
~ In b0 ls -> ~ In b0 rs ->
mem_inv rsegs m ->
evt rsegs (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5fbcc) fc None m (seg_rom rsegs)).
Lemma gw_eq_strcmp_stmt : @strcmp_stmt = ltac:(GwInst.gw_term (@QVbl.Mq5.strcmp_stmt rsegs 0x5fbcc) (@strcmp_stmt)). Proof. unfold strcmp_stmt, QVbl.Mq5.strcmp_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strcmp_stmt : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte).
Hypothesis MI : mem_inv rsegs m.
Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) (ls ++ [b0]).
Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) (rs ++ [b0]).
Hypothesis NL : ~ In b0 ls.
Hypothesis NR : ~ In b0 rs.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Notation A := (bv_unsigned a0).
Notation B := (bv_unsigned a1).
Notation L := (Z.of_nat (length ls)).
Notation R := (Z.of_nat (length rs)).
Notation POST := (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs m).

Notation ST pc x10 x11 x12 x13 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

#[using="m LS RS"] Lemma bounds : (0 <= A /\ A + L + 1 <= 2^64 /\ 0 <= B /\ B + R + 1 <= 2^64)%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.bounds rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma full_nth : ltac2:(Q6nq.tyx '(@QVbl.Mq5.full_nth rsegs 0x5fbcc gw_code gw_base4 gw_baser) [[@gw_eq_strcmp_entry__3; @gw_eq_strcmp_entry__2; @gw_eq_strcmp_entry]; [@gw_eq_strcmp_post__3; @gw_eq_strcmp_post__2; @gw_eq_strcmp_post]; [@gw_eq_strcmp_stmt__3; @gw_eq_strcmp_stmt__2; @gw_eq_strcmp_stmt]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.full_nth rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma walk_at : ltac2:(Q6nq.tyx '(@QVbl.Mq5.walk_at rsegs 0x5fbcc gw_code gw_base4 gw_baser) [[@gw_eq_strcmp_entry__3; @gw_eq_strcmp_entry__2; @gw_eq_strcmp_entry]; [@gw_eq_strcmp_post__3; @gw_eq_strcmp_post__2; @gw_eq_strcmp_post]; [@gw_eq_strcmp_stmt__3; @gw_eq_strcmp_stmt__2; @gw_eq_strcmp_stmt]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.walk_at rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.

#[using="MI LS RS MU WM"] Lemma strcmp_ret : ltac2:(Q6nq.tyx '(@QVbl.Mq5.strcmp_ret rsegs 0x5fbcc gw_code gw_base4 gw_baser) [[@gw_eq_strcmp_entry__3; @gw_eq_strcmp_entry__2; @gw_eq_strcmp_entry]; [@gw_eq_strcmp_post__3; @gw_eq_strcmp_post__2; @gw_eq_strcmp_post]; [@gw_eq_strcmp_stmt__3; @gw_eq_strcmp_stmt__2; @gw_eq_strcmp_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392188]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.strcmp_ret rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.

#[using="MI LS RS NL NR MU WM"] Lemma strcmp_loop : ltac2:(Q6nq.tyx '(@QVbl.Mq5.strcmp_loop rsegs 0x5fbcc gw_code gw_base4 gw_baser) [[@gw_eq_strcmp_entry__3; @gw_eq_strcmp_entry__2; @gw_eq_strcmp_entry]; [@gw_eq_strcmp_post__3; @gw_eq_strcmp_post__2; @gw_eq_strcmp_post]; [@gw_eq_strcmp_stmt__3; @gw_eq_strcmp_stmt__2; @gw_eq_strcmp_stmt]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392164]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.strcmp_loop rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.

#[using="MI LS RS NL NR MU WM"] Lemma strcmp_body : evt rsegs POST (ST 0x5fbcc a0 a1 a2 a3).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.strcmp_body rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.
End Proofs.

Lemma strcmp_spec : strcmp_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq5.strcmp_spec rsegs 0x5fbcc gw_code gw_base4 gw_baser). Qed.
