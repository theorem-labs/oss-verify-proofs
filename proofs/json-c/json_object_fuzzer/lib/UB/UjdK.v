(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Lemma gw_code : CodeAt.code_at rsegs 0x5f9b8 QVbl.Mq4.memset_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5f9b8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5f9b8 /\ 0x5f9b8 + 248 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition memset_entry := 0x5f9b8%Z.
Lemma gw_eq_memset_entry : @memset_entry = ltac:(GwInst.gw_term (@QVbl.Mq4.memset_entry 0x5f9b8) (@memset_entry)). Proof. unfold memset_entry, QVbl.Mq4.memset_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memset_entry : gw_eqs.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq4.land4_of_aligned rsegs 0x5f9b8 gw_code gw_base4 gw_baser). Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].
Lemma gw_eq_memset_post : @memset_post = ltac:(GwInst.gw_term (@QVbl.Mq4.memset_post rsegs) (@memset_post)). Proof. unfold memset_post, QVbl.Mq4.memset_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memset_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).

Lemma memset_loop : ltac2:(Q6nq.tyx '(@QVbl.Mq4.memset_loop rsegs 0x5f9b8 gw_code gw_base4 gw_baser) [[@gw_eq_memset_entry__3; @gw_eq_memset_entry__2; @gw_eq_memset_entry]; [@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]] '([256; 391824]%Z : list Z) '(Q6nq.gwt_zc BC8 Q6nq.gwt_nil)).
Proof using AB. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq4.memset_loop rsegs 0x5f9b8 gw_code gw_base4 gw_baser). Qed.

Lemma memset_body : ltac2:(Q6nq.tyx '(@QVbl.Mq4.memset_body rsegs 0x5f9b8 gw_code gw_base4 gw_baser) [[@gw_eq_memset_entry__3; @gw_eq_memset_entry__2; @gw_eq_memset_entry]; [@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391608]%Z : list Z) '(Q6nq.gwt_unf (@memset_entry) Q6nq.gwt_nil)).
Proof using AB MI0. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq4.memset_body rsegs 0x5f9b8 gw_code gw_base4 gw_baser). Qed.
End Proofs.

Lemma memset_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq4.memset_spec rsegs 0x5f9b8 gw_code gw_base4 gw_baser) [[@gw_eq_memset_entry__3; @gw_eq_memset_entry__2; @gw_eq_memset_entry]; [@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]] '([391608]%Z : list Z) '(Q6nq.gwt_unf (@memset_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq4.memset_spec rsegs 0x5f9b8 gw_code gw_base4 gw_baser). Qed.
