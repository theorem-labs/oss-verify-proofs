(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Lemma gw_code : CodeAt.code_at rsegs 0x581f0 QVbl.Mq1.getf2_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x581f0 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x581f0 /\ 0x581f0 + 188 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition getf2_entry := 0x581f0%Z.
Lemma gw_eq_getf2_entry : @getf2_entry = ltac:(GwInst.gw_term (@QVbl.Mq1.getf2_entry 0x581f0) (@getf2_entry)). Proof. unfold getf2_entry, QVbl.Mq1.getf2_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_getf2_entry : gw_eqs.

Definition ge_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.
Lemma gw_eq_ge_isnan_w : @ge_isnan_w = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_isnan_w) (@ge_isnan_w)). Proof. unfold ge_isnan_w, QVbl.Mq1.ge_isnan_w; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_ge_isnan_w : gw_eqs.

Definition ge_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.
Lemma gw_eq_ge_isless : @ge_isless = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_isless) (@ge_isless)). Proof. unfold ge_isless, QVbl.Mq1.ge_isless; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_ge_isless : gw_eqs.

Definition ge_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).
Lemma gw_eq_ge_tail : @ge_tail = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_tail) (@ge_tail)). Proof. unfold ge_tail, QVbl.Mq1.ge_tail; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_ge_tail : gw_eqs.

Definition ge_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else ge_tail (ge_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.
Lemma gw_eq_ge_core : @ge_core = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_core) (@ge_core)). Proof. unfold ge_core, QVbl.Mq1.ge_core; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_ge_core : gw_eqs.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.lo64_words rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.hi64_words rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma f128_ge_split : ltac2:(Q6nq.tyx '(@QVbl.Mq1.f128_ge_split rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.f128_ge_split rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.b2z_snez rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Definition getf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_getf2_post : @getf2_post = ltac:(GwInst.gw_term (@QVbl.Mq1.getf2_post rsegs) (@getf2_post)). Proof. unfold getf2_post, QVbl.Mq1.getf2_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_getf2_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv rsegs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Lemma getf2_L54 : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_L54 rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([361112]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_L54 rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma getf2_Lcc : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_Lcc rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([360976]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_Lcc rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma getf2_L00 : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_L00 rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([361028]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_L00 rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.

Lemma getf2_Ldc : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_Ldc rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([360992]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_Ldc rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.
End Proofs.

Lemma getf2_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_spec rsegs 0x581f0 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]] '([360944]%Z : list Z) '(Q6nq.gwt_unf (@getf2_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_spec rsegs 0x581f0 gw_code gw_base4 gw_baser). Qed.
