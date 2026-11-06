(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.

Module GwI.
Definition segs := usegs.
Definition base := 0xdd914%Z.
Definition w_22 := 0xfff33697%Z.
Definition w_23 := 0xa646b683%Z.
Definition w_24 := 0xfff33717%Z.
Definition w_25 := 0xa4473703%Z.
Definition hi_22 := (Z_to_bv 20 1048371).
Definition hi_24 := (Z_to_bv 20 1048371).
Definition lo_23 := (Z_to_bv 12 2660).
Definition lo_25 := (Z_to_bv 12 2628).
Definition G_10780 := 0x103b8%Z.
Definition G_10790 := 0x103d0%Z.
Lemma CODE : CodeAt.code_at usegs 0xdd914 (QQLG.Mq8.memchr_code 0xfff33697%Z 0xa646b683%Z 0xfff33717%Z 0xa4473703%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0xdd914 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0xdd914 /\ 0xdd914 + 204 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition memchr_entry := 0xdd914%Z.
Lemma gw_eq_memchr_entry : @memchr_entry = ltac:(GwInst.gw_term (@QQLG.Mq8.memchr_entry 0xdd914) (@memchr_entry)). Proof. unfold memchr_entry, QQLG.Mq8.memchr_entry; autorewrite with gw_eqs; reflexivity. Qed.
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
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ bytes_at usegs m' (bv_unsigned a0) buf.
Lemma gw_eq_memchr_post : @memchr_post = ltac:(GwInst.gw_term (@QQLG.Mq8.memchr_post usegs) (@memchr_post)). Proof. unfold memchr_post, QQLG.Mq8.memchr_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memchr_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
Hypothesis MI : mem_inv usegs m.
Hypothesis BUF : bytes_at usegs m (bv_unsigned a0) buf.
Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono usegs m m := wmono_refl usegs m.

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

#[using="MI BUF OK MU WM"] Lemma memchr_tail : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_tail) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907700]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_tail). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_tail_entry : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_tail_entry) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907692]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_tail_entry). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_words : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_words) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907656]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_words). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_mid : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_mid) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907608]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_mid). Qed.

#[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.b2z_word_zero_iff). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_head : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_head) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907568]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_head). Qed.

#[using="MI BUF OK MU WM"] Lemma memchr_body : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_body) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([907540]%Z : list Z) '(Q6nq.gwt_unf (@memchr_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_body). Qed.
End Proofs.
Lemma gw_eq_NOB__2 : @NOB = ltac:(GwInst.gw_term (@QQLG.Mq8.NOB) (@NOB)). Proof. unfold NOB, QQLG.Mq8.NOB; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_NOB__2 : gw_eqs.

Lemma memchr_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq8.memchr_spec) [[@gw_eq_memchr_entry__3; @gw_eq_memchr_entry__2; @gw_eq_memchr_entry]; [@gw_eq_memchr_post__3; @gw_eq_memchr_post__2; @gw_eq_memchr_post]; [@gw_eq_NOB__3; @gw_eq_NOB__2; @gw_eq_NOB]] '([256; 907540]%Z : list Z) '(Q6nq.gwt_unf (@memchr_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq8.memchr_spec). Qed.
