(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5fc5c%Z.
Definition w_15 := 0xfffb3597%Z.
Definition w_16 := 0xfffb3717%Z.
Definition w_17 := 0x7885b683%Z.
Definition w_18 := 0x77473703%Z.
Definition hi_15 := (Z_to_bv 20 1048499).
Definition hi_16 := (Z_to_bv 20 1048499).
Definition lo_17 := (Z_to_bv 12 1928).
Definition lo_18 := (Z_to_bv 12 1908).
Definition G_10780 := 0x13410%Z.
Definition G_10790 := 0x13420%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5fc5c (QQLG.Mqb.strlen_code 0xfffb3597%Z 0xfffb3717%Z 0x7885b683%Z 0x77473703%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5fc5c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5fc5c /\ 0x5fc5c + 144 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition strlen_entry := 0x5fc5c%Z.
Lemma gw_eq_strlen_entry : @strlen_entry = ltac:(GwInst.gw_term (@QQLG.Mqb.strlen_entry 0x5fc5c) (@strlen_entry)). Proof. unfold strlen_entry, QQLG.Mqb.strlen_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strlen_entry : gw_eqs.

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
Lemma gw_eq_strlen_post : @strlen_post = ltac:(GwInst.gw_term (@QQLG.Mqb.strlen_post rsegs) (@strlen_post)). Proof. unfold strlen_post, QQLG.Mqb.strlen_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_strlen_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
Hypothesis MI : mem_inv rsegs m.
Hypothesis STR : bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Notation A := (bv_unsigned a0).
Notation len := (Z.of_nat (length str)).
Notation full := (str ++ Z_to_bv 8 0 :: slack).

#[using="a0"] Lemma full_length : length full = (length str + S (length slack))%nat.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.full_length). Qed.

#[using="m STR"] Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.A_bound). Qed.

#[using="a0 NONUL"] Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.full_nth_lt). Qed.

#[using="a0"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.full_nth_len). Qed.

#[using="MI STR NONUL MU WM"] Lemma strlen_tail : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqb.strlen_tail) [[@gw_eq_strlen_entry__3; @gw_eq_strlen_entry__2; @gw_eq_strlen_entry]; [@gw_eq_strlen_post__3; @gw_eq_strlen_post__2; @gw_eq_strlen_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392396]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.strlen_tail). Qed.

#[using="MI STR NONUL PAD MU WM"] Lemma strlen_words : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqb.strlen_words) [[@gw_eq_strlen_entry__3; @gw_eq_strlen_entry__2; @gw_eq_strlen_entry]; [@gw_eq_strlen_post__3; @gw_eq_strlen_post__2; @gw_eq_strlen_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392368]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.strlen_words). Qed.

#[using="MI STR NONUL PAD MU WM"] Lemma strlen_wentry : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqb.strlen_wentry) [[@gw_eq_strlen_entry__3; @gw_eq_strlen_entry__2; @gw_eq_strlen_entry]; [@gw_eq_strlen_post__3; @gw_eq_strlen_post__2; @gw_eq_strlen_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392344]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.strlen_wentry). Qed.

#[using="MI STR NONUL PAD MU WM"] Lemma strlen_head : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqb.strlen_head) [[@gw_eq_strlen_entry__3; @gw_eq_strlen_entry__2; @gw_eq_strlen_entry]; [@gw_eq_strlen_post__3; @gw_eq_strlen_post__2; @gw_eq_strlen_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([392312]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.strlen_head). Qed.
End Proofs.

Lemma strlen_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mqb.strlen_spec) [[@gw_eq_strlen_entry__3; @gw_eq_strlen_entry__2; @gw_eq_strlen_entry]; [@gw_eq_strlen_post__3; @gw_eq_strlen_post__2; @gw_eq_strlen_post]] '([392284]%Z : list Z) '(Q6nq.gwt_unf (@strlen_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mqb.strlen_spec). Qed.
