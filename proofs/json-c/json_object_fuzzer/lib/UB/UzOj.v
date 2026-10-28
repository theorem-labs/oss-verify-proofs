(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UL4p.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x56454%Z.
Definition w_4 := 0xfffc0697%Z.
Definition w_5 := 0x26c68693%Z.
Definition hi_4 := (Z_to_bv 20 1048512).
Definition lo_5 := (Z_to_bv 12 620).
Definition G_11878 := 0x166d0%Z.
Definition jt_11878_o40 := 261548%Z.
Definition jt_11878_o284 := 261792%Z.
Definition jt_11878_o148 := 261656%Z.
Definition jt_11878_o64 := 261572%Z.
Lemma CODE : CodeAt.code_at rsegs 0x56454 (Q91D.Mq3.pop_arg_code 0xfffc0697%Z 0x26c68693%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x56454 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x56454 /\ 0x56454 + 308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition extenddftf2_spec := @extenddftf2_spec.
Lemma ROM_jt_11878_0 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_0). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_jt_11878_1 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_1). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_jt_11878_2 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_2). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_jt_11878_4 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_4). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_jt_11878_5 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_5). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_jt_11878_16 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q91D.Mq3.gw_all) @ROM_jt_11878_16). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Definition pop_arg_entry := 0x56454%Z.
Lemma gw_eq_pop_arg_entry : @pop_arg_entry = ltac:(GwInst.gw_term (@Q91D.Mq3.pop_arg_entry 0x56454) (@pop_arg_entry)). Proof. unfold pop_arg_entry, Q91D.Mq3.pop_arg_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pop_arg_entry : gw_eqs.
Definition T_PTR := 9%Z.
Lemma gw_eq_T_PTR : @T_PTR = ltac:(GwInst.gw_term (@Q91D.Mq3.T_PTR) (@T_PTR)). Proof. unfold T_PTR, Q91D.Mq3.T_PTR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_T_PTR : gw_eqs. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.
Definition T_LONG := 13%Z.
Lemma gw_eq_T_LONG : @T_LONG = ltac:(GwInst.gw_term (@Q91D.Mq3.T_LONG) (@T_LONG)). Proof. unfold T_LONG, Q91D.Mq3.T_LONG; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_T_LONG : gw_eqs. Definition T_ULONG := 14%Z.

Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
bytes_at rsegs m VA (u64s slots).
Lemma gw_eq_va_area : @va_area = ltac:(GwInst.gw_term (@Q91D.Mq3.va_area rsegs) (@va_area)). Proof. unfold va_area, Q91D.Mq3.va_area; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_va_area : gw_eqs.

Definition pop_arg_lo (ty : Z) (slot : word) : word :=
if ((ty =? T_PTR) || (ty =? T_LONG) || (ty =? T_ULONG))%Z%bool then slot
else if (ty =? T_INT)%Z then sx32 slot
else if (ty =? T_UINT)%Z then zx32 slot
else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Lemma gw_eq_pop_arg_lo : @pop_arg_lo = ltac:(GwInst.gw_term (@Q91D.Mq3.pop_arg_lo) (@pop_arg_lo)). Proof. unfold pop_arg_lo, Q91D.Mq3.pop_arg_lo; rewrite ?gw_eq_T_PTR, ?gw_eq_T_LONG; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pop_arg_lo : gw_eqs.
Definition pop_arg_hi (ty : Z) (slot y : word) : word :=
if (ty =? T_DBL)%Z then Z_to_bv 64 (hi64 (f128_of_d (bv_unsigned slot))) else y.
Lemma gw_eq_pop_arg_hi : @pop_arg_hi = ltac:(GwInst.gw_term (@Q91D.Mq3.pop_arg_hi) (@pop_arg_hi)). Proof. unfold pop_arg_hi, Q91D.Mq3.pop_arg_hi; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pop_arg_hi : gw_eqs.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
/\ rw_cells rsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
/\ rw_cells rsegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
/\ va_area m' VA slots
/\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).
Lemma gw_eq_pop_arg_post : @pop_arg_post = ltac:(GwInst.gw_term (@Q91D.Mq3.pop_arg_post rsegs) (@pop_arg_post)). Proof. unfold pop_arg_post, Q91D.Mq3.pop_arg_post; rewrite ?gw_eq_va_area, ?gw_eq_pop_arg_lo, ?gw_eq_pop_arg_hi; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_pop_arg_post : gw_eqs.

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. first [GwInst.gw_exact (@Q91D.Mq3.firstn4_le8) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq3.firstn4_le8)]. Qed.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma va_read8 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq3.va_read8) [[@gw_eq_pop_arg_entry__3; @gw_eq_pop_arg_entry__2; @gw_eq_pop_arg_entry]; [@gw_eq_T_PTR__3; @gw_eq_T_PTR__2; @gw_eq_T_PTR]; [@gw_eq_T_LONG__3; @gw_eq_T_LONG__2; @gw_eq_T_LONG]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_pop_arg_lo__3; @gw_eq_pop_arg_lo__2; @gw_eq_pop_arg_lo]; [@gw_eq_pop_arg_hi__3; @gw_eq_pop_arg_hi__2; @gw_eq_pop_arg_hi]; [@gw_eq_pop_arg_post__3; @gw_eq_pop_arg_post__2; @gw_eq_pop_arg_post]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_read8) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_read8)]. Qed.

Lemma va_read4 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq3.va_read4) [[@gw_eq_pop_arg_entry__3; @gw_eq_pop_arg_entry__2; @gw_eq_pop_arg_entry]; [@gw_eq_T_PTR__3; @gw_eq_T_PTR__2; @gw_eq_T_PTR]; [@gw_eq_T_LONG__3; @gw_eq_T_LONG__2; @gw_eq_T_LONG]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_pop_arg_lo__3; @gw_eq_pop_arg_lo__2; @gw_eq_pop_arg_lo]; [@gw_eq_pop_arg_hi__3; @gw_eq_pop_arg_hi__2; @gw_eq_pop_arg_hi]; [@gw_eq_pop_arg_post__3; @gw_eq_pop_arg_post__2; @gw_eq_pop_arg_post]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_read4) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_read4)]. Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. rewrite ?gw_eq_va_area; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_area_bound) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq3.va_area_bound)]. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_1 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Lemma pop_arg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
rw_cells rsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
rw_cells rsegs m (bv_unsigned a0) [C8 x; C8 y] ->
stk rsegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
mem_inv rsegs m ->
a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL \/ ty = T_LONG \/ ty = T_ULONG) ->
(16 <= bv_unsigned sp)%Z ->
(bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x56454) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_T_PTR, ?gw_eq_T_LONG, ?gw_eq_va_area, ?gw_eq_pop_arg_post; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq3.pop_arg_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq3.pop_arg_spec)]. Qed.
