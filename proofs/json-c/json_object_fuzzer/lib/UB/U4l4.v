(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification.
Lemma gw_code : CodeAt.code_at rsegs 0x5f438 QVbl.Mq3.memcpy_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5f438 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5f438 /\ 0x5f438 + 1028 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition memcpy_entry := 0x5f438%Z.
Lemma gw_eq_memcpy_entry : @memcpy_entry = ltac:(GwInst.gw_term (@QVbl.Mq3.memcpy_entry 0x5f438) (@memcpy_entry)). Proof. unfold memcpy_entry, QVbl.Mq3.memcpy_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memcpy_entry : gw_eqs.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.
Lemma gw_eq_memcpy_post : @memcpy_post = ltac:(GwInst.gw_term (@QVbl.Mq3.memcpy_post rsegs) (@memcpy_post)). Proof. unfold memcpy_post, QVbl.Mq3.memcpy_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memcpy_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.
Lemma gw_eq_INV : @INV = ltac:(GwInst.gw_term (@QVbl.Mq3.INV rsegs) (@INV)). Proof. unfold INV, QVbl.Mq3.INV; autorewrite with gw_eqs; reflexivity. Qed.
#[local] Hint Rewrite gw_eq_INV : gw_eqs.

Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

Lemma mc_a8c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a8c rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391160]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a8c rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a60 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a60 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391116]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a60 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a58 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a58 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391108]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a58 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a0c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a0c rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391032]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a0c rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_734 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_734 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390304]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_734 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a04 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a04 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([391024]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a04 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_72c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_72c rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390296]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_72c rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_978 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_978 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390884]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_978 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_848 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_848 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390580]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_848 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_828 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_828 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390548]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_828 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_7f8 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_7f8 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390500]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_7f8 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_7ec : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_7ec rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390488]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_7ec rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_770 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_770 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390364]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_770 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_754 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_754 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390336]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_754 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_878 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_878 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390628]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_878 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_864 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_864 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390608]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_864 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_90c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_90c rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390776]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_90c rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_8e8 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_8e8 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390740]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_8e8 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_740 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_740 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390316]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_740 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_71c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_71c rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390280]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_71c rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_714 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_714 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390272]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_714 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma mc_6e4 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_6e4 rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390224]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_6e4 rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.

Lemma memcpy_body : ltac2:(Q6nq.tyx '(@QVbl.Mq3.memcpy_body rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) Q6nq.gwt_nil)).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.memcpy_body rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.
End Proofs.
Lemma gw_eq_INV__2 : @INV = ltac:(GwInst.gw_term (@QVbl.Mq3.INV rsegs) (@INV)). Proof. unfold INV, QVbl.Mq3.INV; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_INV__2 : gw_eqs.

Lemma memcpy_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq3.memcpy_spec rsegs 0x5f438 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.memcpy_spec rsegs 0x5f438 gw_code gw_base4 gw_baser). Qed.
