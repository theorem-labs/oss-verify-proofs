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
Lemma gw_code : CodeAt.code_at rsegs 0x58128 QVbl.Mq2.letf2_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x58128 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x58128 /\ 0x58128 + 200 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition letf2_entry := 0x58128%Z.
Lemma gw_eq_letf2_entry : @letf2_entry = ltac:(GwInst.gw_term (@QVbl.Mq2.letf2_entry 0x58128) (@letf2_entry)). Proof. unfold letf2_entry, QVbl.Mq2.letf2_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_letf2_entry : gw_eqs.

Definition f128_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.
Lemma gw_eq_f128_isnan_w : @f128_isnan_w = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_isnan_w) (@f128_isnan_w)). Proof. unfold f128_isnan_w, QVbl.Mq2.f128_isnan_w; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_f128_isnan_w : gw_eqs.

Definition f128_le_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.
Lemma gw_eq_f128_le_isless : @f128_le_isless = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_isless) (@f128_le_isless)). Proof. unfold f128_le_isless, QVbl.Mq2.f128_le_isless; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_f128_le_isless : gw_eqs.

Definition f128_le_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).
Lemma gw_eq_f128_le_tail : @f128_le_tail = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_tail) (@f128_le_tail)). Proof. unfold f128_le_tail, QVbl.Mq2.f128_le_tail; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_f128_le_tail : gw_eqs.

Definition f128_le_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else f128_le_tail (f128_le_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.
Lemma gw_eq_f128_le_core : @f128_le_core = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_core) (@f128_le_core)). Proof. unfold f128_le_core, QVbl.Mq2.f128_le_core; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_f128_le_core : gw_eqs.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.lo64_words rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.hi64_words rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Lemma f128_le_split : ltac2:(Q6nq.tyx '(@QVbl.Mq2.f128_le_split rsegs 0x58128 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.f128_le_split rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.b2z_snez rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Definition letf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_letf2_post : @letf2_post = ltac:(GwInst.gw_term (@QVbl.Mq2.letf2_post rsegs) (@letf2_post)). Proof. unfold letf2_post, QVbl.Mq2.letf2_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_letf2_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv rsegs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono rsegs m m := wmono_refl rsegs m.

Lemma letf2_L98 : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L98 rsegs 0x58128 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([360924]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L98 rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Lemma letf2_L40 : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L40 rsegs 0x58128 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([360836]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L40 rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.

Lemma letf2_L1c : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L1c rsegs 0x58128 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]] '([360800]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L1c rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.
End Proofs.

Lemma letf2_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_spec rsegs 0x58128 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]] '([360744]%Z : list Z) '(Q6nq.gwt_unf (@letf2_entry) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_spec rsegs 0x58128 gw_code gw_base4 gw_baser). Qed.
