(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification.
Lemma gw_code : CodeAt.code_at usegs 0xdda10 QVbl.Mq3.memcpy_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xdda10 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xdda10 /\ 0xdda10 + 1028 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Definition memcpy_entry := 0xdda10%Z.
Lemma gw_eq_memcpy_entry : @memcpy_entry = ltac:(GwInst.gw_term (@QVbl.Mq3.memcpy_entry 0xdda10) (@memcpy_entry)). Proof. unfold memcpy_entry, QVbl.Mq3.memcpy_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memcpy_entry : gw_eqs.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at usegs m' (bv_unsigned a1) src.
Lemma gw_eq_memcpy_post : @memcpy_post = ltac:(GwInst.gw_term (@QVbl.Mq3.memcpy_post usegs) (@memcpy_post)). Proof. unfold memcpy_post, QVbl.Mq3.memcpy_post; autorewrite with gw_eqs; reflexivity. Qed.
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
bytes_at usegs m1 S src /\ u8arr usegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv usegs m1 /\ munch W m m1 /\ wmono usegs m m1.
Lemma gw_eq_INV : @INV = ltac:(GwInst.gw_term (@QVbl.Mq3.INV usegs) (@INV)). Proof. unfold INV, QVbl.Mq3.INV; autorewrite with gw_eqs; reflexivity. Qed.
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

Lemma mc_a8c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a8c usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908752]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a8c usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a60 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a60 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908708]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a60 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a58 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a58 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908700]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a58 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a0c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a0c usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908624]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a0c usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_734 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_734 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907896]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_734 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_a04 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_a04 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908616]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_a04 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_72c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_72c usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907888]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_72c usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_978 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_978 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908476]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_978 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_848 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_848 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908172]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_848 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_828 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_828 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908140]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_828 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_7f8 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_7f8 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908092]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_7f8 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_7ec : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_7ec usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908080]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_7ec usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_770 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_770 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907956]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_770 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_754 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_754 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907928]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_754 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_878 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_878 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908220]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_878 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_864 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_864 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908200]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_864 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_90c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_90c usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908368]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_90c usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_8e8 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_8e8 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([908332]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_8e8 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_740 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_740 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907908]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_740 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_71c : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_71c usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907872]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_71c usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_714 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_714 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907864]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_714 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma mc_6e4 : ltac2:(Q6nq.tyx '(@QVbl.Mq3.mc_6e4 usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907816]%Z : list Z) 'Q6nq.gwt_nil).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.mc_6e4 usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.

Lemma memcpy_body : ltac2:(Q6nq.tyx '(@QVbl.Mq3.memcpy_body usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907792]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) Q6nq.gwt_nil)).
Proof using AB LEN SEP. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.memcpy_body usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.
End Proofs.
Lemma gw_eq_INV__2 : @INV = ltac:(GwInst.gw_term (@QVbl.Mq3.INV usegs) (@INV)). Proof. unfold INV, QVbl.Mq3.INV; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_INV__2 : gw_eqs.

Lemma memcpy_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq3.memcpy_spec usegs 0xdda10 gw_code gw_base4 gw_baser) [[@gw_eq_memcpy_entry__3; @gw_eq_memcpy_entry__2; @gw_eq_memcpy_entry]; [@gw_eq_memcpy_post__3; @gw_eq_memcpy_post__2; @gw_eq_memcpy_post]; [@gw_eq_INV__3; @gw_eq_INV__2; @gw_eq_INV]] '([907792]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq3.memcpy_spec usegs 0xdda10 gw_code gw_base4 gw_baser). Qed.
