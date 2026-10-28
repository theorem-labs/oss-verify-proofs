(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5f33c%Z.
Definition w_22 := 0xfffb4697%Z.
Definition w_23 := 0x08c6b683%Z.
Definition w_24 := 0xfffb4717%Z.
Definition w_25 := 0x07473703%Z.
Definition hi_22 := (Z_to_bv 20 1048500).
Definition hi_24 := (Z_to_bv 20 1048500).
Definition lo_23 := (Z_to_bv 12 140).
Definition lo_25 := (Z_to_bv 12 116).
Definition G_10780 := 0x13410%Z.
Definition G_10790 := 0x13420%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5f33c (QQLG.Mq8.memchr_code 0xfffb4697%Z 0x08c6b683%Z 0xfffb4717%Z 0x07473703%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5f33c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5f33c /\ 0x5f33c + 204 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition memchr_entry := 0x5f33c%Z.
Lemma gw_eq_memchr_entry : @memchr_entry = ltac:(GwInst.gw_term (@QQLG.Mq8.memchr_entry 0x5f33c) (@memchr_entry)). Proof. unfold memchr_entry, QQLG.Mq8.memchr_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memchr_entry : gw_eqs.

Section ZFacts.
Open Scope Z_scope.
#[using="Type"] Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.lxor_lt_256). Qed.

#[using="Type"] Lemma lxor_split : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.lxor_split) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]] '([256]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.lxor_split). Qed.

#[using="Type"] Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.le_val_nonneg). Qed.

#[using="Type"] Lemma le_val_xor_bcast : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.le_val_xor_bcast) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]] '([256]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.le_val_xor_bcast). Qed.

#[using="Type"] Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.bytes_ok_xor). Qed.

#[using="Type"] Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.In0_xor). Qed.
End ZFacts.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bytes_at rsegs m' (bv_unsigned a0) buf.
Lemma gw_eq_memchr_post : @memchr_post = ltac:(GwInst.gw_term (@QQLG.Mq8.memchr_post rsegs) (@memchr_post)). Proof. unfold memchr_post, QQLG.Mq8.memchr_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memchr_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
Hypothesis MI : mem_inv rsegs m.
Hypothesis BUF : bytes_at rsegs m (bv_unsigned a0) buf.
Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation c := ((bv_unsigned a1) mod 256)%Z.
Notation len := (Z.of_nat (length buf)).

Definition NOB (i : Z) : Prop :=
forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.
Lemma gw_eq_NOB : @NOB = ltac:(GwInst.gw_term (@QQLG.Mq8.NOB) (@NOB)). Proof. unfold NOB, QQLG.Mq8.NOB; autorewrite with gw_eqs; reflexivity. Qed.
#[local] Hint Rewrite gw_eq_NOB : gw_eqs.

#[using="m BUF"] Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.A_bound). Qed.

#[using="Type"] Lemma NOB_0 : NOB 0.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.NOB_0). Qed.

#[using="Type"] Lemma NOB_S : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.NOB_S) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.NOB_S). Qed.

#[using="OK"] Lemma ok_cases : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.ok_cases) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.ok_cases). Qed.

#[using="a0 OK"] Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.readable). Qed.

#[using="OK"] Lemma readable8 : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.readable8) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.readable8). Qed.

#[using="Type"] Lemma res_found : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.res_found) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.res_found). Qed.

#[using="Type"] Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.res_none). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_tail : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_tail) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390108]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_tail). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_tail_entry : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_tail_entry) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390100]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_tail_entry). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_words : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_words) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390064]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_words). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_mid : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_mid) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([390016]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_mid). Qed.

#[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.b2z_word_zero_iff). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_head : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_head) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([389976]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_head). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_body : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_body) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([389948]%Z : list Z) '(Q6nq.gwt_unf (@memchr_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_body). Qed.
End Proofs.
Lemma gw_eq_NOB__2 : @NOB = ltac:(GwInst.gw_term (@QQLG.Mq8.NOB) (@NOB)). Proof. unfold NOB, QQLG.Mq8.NOB; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_NOB__2 : gw_eqs.

Lemma memchr_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_spec) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '([256; 389948]%Z : list Z) '(Q6nq.gwt_unf (@memchr_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_spec). Qed.
