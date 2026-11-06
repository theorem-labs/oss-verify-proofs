(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at usegs 0xd1ca8 QVbl.Mq2.letf2_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd1ca8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd1ca8 /\ 0xd1ca8 + 200 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition letf2_entry := 0xd1ca8%Z.
Lemma gw_eq_letf2_entry : @letf2_entry = ltac:(GwInst.gw_term (@QVbl.Mq2.letf2_entry 0xd1ca8) (@letf2_entry)). Proof. unfold letf2_entry, QVbl.Mq2.letf2_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_letf2_entry : gw_eqs.

Definition f128_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.
Lemma gw_eq_f128_isnan_w : @f128_isnan_w = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_isnan_w) (@f128_isnan_w)). Proof. unfold f128_isnan_w, QVbl.Mq2.f128_isnan_w; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_f128_isnan_w : gw_eqs.

Definition f128_le_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.
Lemma gw_eq_f128_le_isless : @f128_le_isless = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_isless) (@f128_le_isless)). Proof. unfold f128_le_isless, QVbl.Mq2.f128_le_isless; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_f128_le_isless : gw_eqs.

Definition f128_le_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).
Lemma gw_eq_f128_le_tail : @f128_le_tail = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_tail) (@f128_le_tail)). Proof. unfold f128_le_tail, QVbl.Mq2.f128_le_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_f128_le_tail : gw_eqs.

Definition f128_le_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else f128_le_tail (f128_le_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.
Lemma gw_eq_f128_le_core : @f128_le_core = ltac:(GwInst.gw_term (@QVbl.Mq2.f128_le_core) (@f128_le_core)). Proof. unfold f128_le_core, QVbl.Mq2.f128_le_core; rewrite ?gw_eq_f128_le_isless, ?gw_eq_f128_le_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_f128_le_core : gw_eqs.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof. first [GwInst.gw_exact (@QVbl.Mq2.lo64_words usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.lo64_words usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof. first [GwInst.gw_exact (@QVbl.Mq2.hi64_words usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.hi64_words usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Lemma f128_le_split : ltac2:(Q6nq.tyx '(@QVbl.Mq2.f128_le_split usegs 0xd1ca8 gw_code gw_base4 gw_baser) [[@gw_eq_f128_isnan_w]; [@gw_eq_f128_le_core]; [@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_f128_isnan_w, ?gw_eq_f128_le_core; first [GwInst.gw_exact (@QVbl.Mq2.f128_le_split usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.f128_le_split usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof. first [GwInst.gw_exact (@QVbl.Mq2.b2z_snez usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.b2z_snez usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Definition letf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
Lemma gw_eq_letf2_post : @letf2_post = ltac:(GwInst.gw_term (@QVbl.Mq2.letf2_post usegs) (@letf2_post)). Proof. unfold letf2_post, QVbl.Mq2.letf2_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_letf2_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv usegs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono usegs m m := wmono_refl usegs m.

Lemma letf2_L98 : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L98 usegs 0xd1ca8 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]] '([859484]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq2.letf2_L98 usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L98 usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Lemma letf2_L40 : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L40 usegs 0xd1ca8 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_f128_le_core]; [@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]] '([859396]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. rewrite ?gw_eq_f128_le_core; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq2.letf2_L40 usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L40 usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.

Lemma letf2_L1c : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_L1c usegs 0xd1ca8 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_f128_isnan_w]; [@gw_eq_f128_le_core]; [@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_letf2_post__3; @gw_eq_letf2_post__2; @gw_eq_letf2_post]] '([859360]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. rewrite ?gw_eq_f128_isnan_w, ?gw_eq_f128_le_core; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq2.letf2_L1c usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_L1c usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.
End Proofs.

Lemma letf2_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq2.letf2_spec usegs 0xd1ca8 gw_code gw_base4 gw_baser) [[@gw_eq_letf2_post]; [@gw_eq_letf2_entry__3; @gw_eq_letf2_entry__2; @gw_eq_letf2_entry]; [@gw_eq_f128_isnan_w__3; @gw_eq_f128_isnan_w__2; @gw_eq_f128_isnan_w]; [@gw_eq_f128_le_isless__3; @gw_eq_f128_le_isless__2; @gw_eq_f128_le_isless]; [@gw_eq_f128_le_tail__3; @gw_eq_f128_le_tail__2; @gw_eq_f128_le_tail]; [@gw_eq_f128_le_core__3; @gw_eq_f128_le_core__2; @gw_eq_f128_le_core]] '([859304]%Z : list Z) '(Q6nq.gwt_unf (@letf2_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_letf2_post; first [GwInst.gw_exact (@QVbl.Mq2.letf2_spec usegs 0xd1ca8 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq2.letf2_spec usegs 0xd1ca8 gw_code gw_base4 gw_baser)]. Qed.
