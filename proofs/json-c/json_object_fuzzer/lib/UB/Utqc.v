(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Lemma gw_code : CodeAt.code_at rsegs 0x5fcec QVbl.Mq6.strncasecmp_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5fcec mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5fcec /\ 0x5fcec + 216 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition tolower_entry := 0x5fdb0%Z.
Lemma gw_eq_tolower_entry : @tolower_entry = ltac:(GwInst.gw_term (@QVbl.Mq6.tolower_entry 0x5fcec) (@tolower_entry)). Proof. unfold tolower_entry, QVbl.Mq6.tolower_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_tolower_entry : gw_eqs.
Definition strncasecmp_entry := 0x5fcec%Z.
Lemma gw_eq_strncasecmp_entry : @strncasecmp_entry = ltac:(GwInst.gw_term (@QVbl.Mq6.strncasecmp_entry 0x5fcec) (@strncasecmp_entry)). Proof. unfold strncasecmp_entry, QVbl.Mq6.strncasecmp_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strncasecmp_entry : gw_eqs.

Lemma tolower_code_ok : ltac2:(Q6nq.tyx '(@QVbl.Mq6.tolower_code_ok rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]] '([(-65); 256; 18446744073709551616]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.tolower_code_ok rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

Definition tolower_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(c : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lower8 c)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_tolower_post : @tolower_post = ltac:(GwInst.gw_term (@QVbl.Mq6.tolower_post rsegs) (@tolower_post)). Proof. unfold tolower_post, QVbl.Mq6.tolower_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_tolower_post : gw_eqs.

Definition tolower_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (c : Z),
(0 <= c < 256)%Z ->
mem_inv rsegs m ->
evt rsegs (tolower_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5fdb0) fc None m (seg_rom rsegs)).
Lemma gw_eq_tolower_stmt : @tolower_stmt = ltac:(GwInst.gw_term (@QVbl.Mq6.tolower_stmt rsegs 0x5fcec) (@tolower_stmt)). Proof. unfold tolower_stmt, QVbl.Mq6.tolower_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_tolower_stmt : gw_eqs.

Lemma tolower_spec : tolower_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.tolower_spec rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

Definition strncasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (ls rs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0' = Z_to_bv 64 (strncasecmp_model ls rs (bv_unsigned a2))
/\ stk rsegs m' lo (bv_unsigned sp)
/\ bytes_at rsegs m' (bv_unsigned a0) (ls ++ [b0]) /\ bytes_at rsegs m' (bv_unsigned a1) (rs ++ [b0]).
Lemma gw_eq_strncasecmp_post : @strncasecmp_post = ltac:(GwInst.gw_term (@QVbl.Mq6.strncasecmp_post rsegs) (@strncasecmp_post)). Proof. unfold strncasecmp_post, QVbl.Mq6.strncasecmp_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strncasecmp_post : gw_eqs.

Definition strncasecmp_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (lo : Z),
bytes_at rsegs m (bv_unsigned a0) (ls ++ [b0]) ->
bytes_at rsegs m (bv_unsigned a1) (rs ++ [b0]) ->
~ In b0 ls -> ~ In b0 rs ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z ->
(bv_unsigned a0 + Z.of_nat (length ls) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a1 + Z.of_nat (length rs) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
mem_inv rsegs m ->
evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5fcec) fc None m (seg_rom rsegs)).
Lemma gw_eq_strncasecmp_stmt : @strncasecmp_stmt = ltac:(GwInst.gw_term (@QVbl.Mq6.strncasecmp_stmt rsegs 0x5fcec) (@strncasecmp_stmt)). Proof. unfold strncasecmp_stmt, QVbl.Mq6.strncasecmp_stmt; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strncasecmp_stmt : gw_eqs.

Lemma swrap32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.swrap32_small rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

Section Proofs.

Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (ls rs : list byte) (lo : Z) (junk8 : list byte).
Hypothesis MI : mem_inv rsegs m.
Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) (ls ++ [b0]).
Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) (rs ++ [b0]).
Hypothesis NL : ~ In b0 ls.
Hypothesis NR : ~ In b0 rs.
Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk rsegs m lo (bv_unsigned sp + -48).
Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m0 m.
Hypothesis WM : wmono rsegs m0 m.
Hypothesis N0 : bv_unsigned a2 <> 0%Z.

#[using="ra s0 s1 s2 s3 m junk8 LS RS FR N0"] Lemma bounds : ltac2:(Q6nq.tyx '(@QVbl.Mq6.bounds rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.bounds rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma full_nth : ltac2:(Q6nq.tyx '(@QVbl.Mq6.full_nth rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.full_nth rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

Definition stop (a b : byte) (k : nat) : bool :=
((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
|| negb ((bv_unsigned a =? bv_unsigned b) || (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b))))%Z%bool.
Lemma gw_eq_stop : @stop = ltac:(GwInst.gw_term (@QVbl.Mq6.stop) (@stop)). Proof. unfold stop, QVbl.Mq6.stop; autorewrite with gw_eqs; reflexivity. Qed.
#[local] Hint Rewrite gw_eq_stop : gw_eqs.

#[using="Type"] Lemma walk_at : ltac2:(Q6nq.tyx '(@QVbl.Mq6.walk_at rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]; [@gw_eq_stop__3; @gw_eq_stop__2; @gw_eq_stop]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.walk_at rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

#[using="junk8 MI LS RS FR STK LO MU WM N0"] Lemma ret_seq : ltac2:(Q6nq.tyx '(@QVbl.Mq6.ret_seq rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]; [@gw_eq_stop__3; @gw_eq_stop__2; @gw_eq_stop]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392572]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.ret_seq rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma land255 : forall x, (0 <= x < 256)%Z -> Z.land x 255 = x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.land255 rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

#[using="junk8 MI LS RS FR STK LO MU WM N0"] Lemma exit_seq : ltac2:(Q6nq.tyx '(@QVbl.Mq6.exit_seq rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]; [@gw_eq_stop__3; @gw_eq_stop__2; @gw_eq_stop]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392552]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.exit_seq rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.

#[using="junk8 MI LS RS NL NR FR STK LO MU WM N0"] Lemma check_loop : ltac2:(Q6nq.tyx '(@QVbl.Mq6.check_loop rsegs 0x5fcec gw_code gw_base4 gw_baser) [[@gw_eq_tolower_entry__3; @gw_eq_tolower_entry__2; @gw_eq_tolower_entry]; [@gw_eq_strncasecmp_entry__3; @gw_eq_strncasecmp_entry__2; @gw_eq_strncasecmp_entry]; [@gw_eq_tolower_post__3; @gw_eq_tolower_post__2; @gw_eq_tolower_post]; [@gw_eq_tolower_stmt__3; @gw_eq_tolower_stmt__2; @gw_eq_tolower_stmt]; [@gw_eq_strncasecmp_post__3; @gw_eq_strncasecmp_post__2; @gw_eq_strncasecmp_post]; [@gw_eq_strncasecmp_stmt__3; @gw_eq_strncasecmp_stmt__2; @gw_eq_strncasecmp_stmt]; [@gw_eq_stop__3; @gw_eq_stop__2; @gw_eq_stop]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392500]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.check_loop rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.
End Proofs.
Lemma gw_eq_stop__2 : @stop = ltac:(GwInst.gw_term (@QVbl.Mq6.stop) (@stop)). Proof. unfold stop, QVbl.Mq6.stop; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_stop__2 : gw_eqs.

Lemma strncasecmp_spec : strncasecmp_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq6.strncasecmp_spec rsegs 0x5fcec gw_code gw_base4 gw_baser). Qed.
