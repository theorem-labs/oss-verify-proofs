(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGbx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGbx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UL4p. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5d870%Z.
Definition w_113 := 0xf79fa0ef%Z.
Definition w_118 := 0xee0fa0ef%Z.
Definition w_124 := 0x84dfa0ef%Z.
Definition w_127 := 0xb21fb0ef%Z.
Definition w_142 := 0xd64fa0ef%Z.
Definition w_158 := 0xe40fa0ef%Z.
Definition w_164 := 0xe28fa0ef%Z.
Definition w_179 := 0xf70fa0ef%Z.
Definition w_217 := 0xed8fa0ef%Z.
Definition w_233 := 0xd99fa0ef%Z.
Definition w_236 := 0xe8cfa0ef%Z.
Definition w_278 := 0xde4fa0ef%Z.
Definition w_295 := 0xda0fa0ef%Z.
Definition w_301 := 0xd88fa0ef%Z.
Definition w_318 := 0xd44fa0ef%Z.
Definition w_324 := 0xd2cfa0ef%Z.
Definition w_347 := 0xfffb5517%Z.
Definition w_348 := 0x61453507%Z.
Definition w_349 := 0x890fa0ef%Z.
Definition w_360 := 0xc9cfa0ef%Z.
Definition hi_347 := (Z_to_bv 20 1048501).
Definition lo_348 := (Z_to_bv 12 1556).
Definition joff_113 := (Z_to_bv 21 2076536).
Definition joff_118 := (Z_to_bv 21 2074336).
Definition joff_124 := (Z_to_bv 21 2074700).
Definition joff_127 := (Z_to_bv 21 2079520).
Definition joff_142 := (Z_to_bv 21 2073956).
Definition joff_158 := (Z_to_bv 21 2074176).
Definition joff_164 := (Z_to_bv 21 2074152).
Definition joff_179 := (Z_to_bv 21 2074480).
Definition joff_217 := (Z_to_bv 21 2074328).
Definition joff_233 := (Z_to_bv 21 2076056).
Definition joff_236 := (Z_to_bv 21 2074252).
Definition joff_278 := (Z_to_bv 21 2074084).
Definition joff_295 := (Z_to_bv 21 2074016).
Definition joff_301 := (Z_to_bv 21 2073992).
Definition joff_318 := (Z_to_bv 21 2073924).
Definition joff_324 := (Z_to_bv 21 2073900).
Definition joff_349 := (Z_to_bv 21 2072720).
Definition joff_360 := (Z_to_bv 21 2073756).
Definition G_10768 := 0x133f0%Z.
Definition e_extenddftf2 := 0x57e74%Z.
Definition e_1fcb0 := 0x5800c%Z.
Definition e_1fdcc := 0x58128%Z.
Definition e_multf3 := 0x582ac%Z.
Definition e_20650 := 0x589ac%Z.
Definition e_divtf3 := 0x5958c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5d870 (QQRC.Mq2.fmodlblk_code 0xf79fa0ef%Z 0xee0fa0ef%Z 0x84dfa0ef%Z 0xb21fb0ef%Z 0xd64fa0ef%Z 0xe40fa0ef%Z 0xe28fa0ef%Z 0xf70fa0ef%Z 0xed8fa0ef%Z 0xd99fa0ef%Z 0xe8cfa0ef%Z 0xde4fa0ef%Z 0xda0fa0ef%Z 0xd88fa0ef%Z 0xd44fa0ef%Z 0xd2cfa0ef%Z 0xfffb5517%Z 0x61453507%Z 0x890fa0ef%Z 0xc9cfa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5d870 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5d870 /\ 0x5d870 + 1468 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition extenddftf2_spec := @extenddftf2_spec.
Definition multf3_spec := @multf3_spec.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition SCALBNL : Z := 0x5dcdc.
Lemma gw_eq_SCALBNL : @SCALBNL = ltac:(GwInst.gw_term (@QQRC.Mq2.SCALBNL 0x5d870) (@SCALBNL)). Proof. unfold SCALBNL, QQRC.Mq2.SCALBNL; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SCALBNL : gw_eqs.
Definition COPYSIGNL : Z := 0x5d9cc.
Lemma gw_eq_COPYSIGNL : @COPYSIGNL = ltac:(GwInst.gw_term (@QQRC.Mq2.COPYSIGNL 0x5d870) (@COPYSIGNL)). Proof. unfold COPYSIGNL, QQRC.Mq2.COPYSIGNL; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_COPYSIGNL : gw_eqs.
Definition FABSL : Z := 0x5dcd0.
Lemma gw_eq_FABSL : @FABSL = ltac:(GwInst.gw_term (@QQRC.Mq2.FABSL 0x5d870) (@FABSL)). Proof. unfold FABSL, QQRC.Mq2.FABSL; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FABSL : gw_eqs.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.testbit_small_high) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.testbit_small_high)]. Qed.

Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.lor_low_high) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.lor_low_high)]. Qed.

Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land_highmask) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land_highmask)]. Qed.

Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land_bit63) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land_bit63)]. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land_m63) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land_m63)]. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land_m48) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land_m48)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq2.multf3_stmt) (@UGbx.multf3_stmt) (Q6nq.gwt_def (@QCa8.multf3_stmt) (@UGbx.multf3_stmt) (Q6nq.gwt_def (@QQRC.Mq2.multf3_post) (@Uwbh.multf3_post) (Q6nq.gwt_def (@Q91D.multf3_post) (@Uwbh.multf3_post) (Q6nq.gwt_def (@QQRC.Mq2.leaf2_post) (@UuJ9.leaf2_post) (Q6nq.gwt_def (@Qy8Z.Mq0.leaf2_post) (@UuJ9.leaf2_post) (Q6nq.gwt_def (@QQRC.Mq2.extenddftf2_post) (@UL4p.extenddftf2_post) (Q6nq.gwt_def (@QQLG.Mq1.extenddftf2_post) (@UL4p.extenddftf2_post) (Q6nq.gwt_def (@QQRC.Mq2.call2_post) (@UuJ9.call2_post) (Q6nq.gwt_def (@Qy8Z.Mq0.call2_post) (@UuJ9.call2_post) Q6nq.gwt_nil)))))))))).
Lemma copysign_hi_eq : ltac2:(Q6nq.tyx '(@QQRC.Mq2.copysign_hi_eq) [[@gw_eq_SCALBNL__3; @gw_eq_SCALBNL__2; @gw_eq_SCALBNL]; [@gw_eq_COPYSIGNL__3; @gw_eq_COPYSIGNL__2; @gw_eq_COPYSIGNL]; [@gw_eq_FABSL__3; @gw_eq_FABSL__2; @gw_eq_FABSL]] '([281474976710655; 9223372036854775807; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) (Q6nq.gwt_unf (@ABS_HI) gwt_X)))))).
Proof. first [GwInst.gw_exact (@QQRC.Mq2.copysign_hi_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.copysign_hi_eq)]. Qed.

Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_leafq_post : @leafq_post = ltac:(GwInst.gw_term (@QQRC.Mq2.leafq_post rsegs) (@leafq_post)). Proof. unfold leafq_post, QQRC.Mq2.leafq_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_leafq_post : gw_eqs.

Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land63_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land63_range)]. Qed.

Lemma fabsl_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQRC.Mq2.fabsl_spec) [[@gw_eq_FABSL]; [@gw_eq_leafq_post]; [@gw_eq_SCALBNL__3; @gw_eq_SCALBNL__2; @gw_eq_SCALBNL]; [@gw_eq_COPYSIGNL__3; @gw_eq_COPYSIGNL__2; @gw_eq_COPYSIGNL]] '(@nil Z) '(Q6nq.gwt_zc FABSL gwt_X)).
Proof. rewrite ?gw_eq_FABSL, ?gw_eq_leafq_post; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq2.fabsl_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq2.fabsl_spec)]. Qed.

Lemma copysignl_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQRC.Mq2.copysignl_spec) [[@gw_eq_COPYSIGNL]; [@gw_eq_leafq_post]; [@gw_eq_SCALBNL__3; @gw_eq_SCALBNL__2; @gw_eq_SCALBNL]; [@gw_eq_FABSL__3; @gw_eq_FABSL__2; @gw_eq_FABSL]] '(@nil Z) '(Q6nq.gwt_zc COPYSIGNL gwt_X)).
Proof. rewrite ?gw_eq_COPYSIGNL, ?gw_eq_leafq_post; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq2.copysignl_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq2.copysignl_spec)]. Qed.

Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq2.land_m16) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.land_m16)]. Qed.

Lemma scal_hi_eq : ltac2:(Q6nq.tyx '(@QQRC.Mq2.scal_hi_eq) [[@gw_eq_SCALBNL__3; @gw_eq_SCALBNL__2; @gw_eq_SCALBNL]; [@gw_eq_COPYSIGNL__3; @gw_eq_COPYSIGNL__2; @gw_eq_COPYSIGNL]; [@gw_eq_FABSL__3; @gw_eq_FABSL__2; @gw_eq_FABSL]; [@gw_eq_leafq_post__3; @gw_eq_leafq_post__2; @gw_eq_leafq_post]] '([16383; 65535; 281474976710655; 4611404543450677248; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) gwt_X)))).
Proof. first [GwInst.gw_exact (@QQRC.Mq2.scal_hi_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.scal_hi_eq)]. Qed.
Definition scal_reduce (x n : Z) : Z * Z :=
(if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in
if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in (x, if 16383 <? n then 16383 else n)
else (x, n)
else if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in
if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in (x, if n <? -16382 then -16382 else n)
else (x, n)
else (x, n))%Z.
Lemma gw_eq_scal_reduce : @scal_reduce = ltac:(GwInst.gw_term (@QQRC.Mq2.scal_reduce) (@scal_reduce)). Proof. unfold scal_reduce, QQRC.Mq2.scal_reduce; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scal_reduce : gw_eqs.
Definition U1 : Z := f128_of_d (bv_unsigned D_ONE).
Lemma gw_eq_U1 : @U1 = ltac:(GwInst.gw_term (@QQRC.Mq2.U1) (@U1)). Proof. unfold U1, QQRC.Mq2.U1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_U1 : gw_eqs.
Definition scal_u (n : Z) : Z :=
mk128 (Z.lor (Z.land (hi64 U1) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n)%Z 0xffff) 48)) (lo64 U1).
Lemma gw_eq_scal_u : @scal_u = ltac:(GwInst.gw_term (@QQRC.Mq2.scal_u) (@scal_u)). Proof. unfold scal_u, QQRC.Mq2.scal_u; rewrite ?gw_eq_U1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scal_u : gw_eqs.
Lemma m_scalbnl_eq : forall x n, m_scalbnl x n = f128_mul (fst (scal_reduce x n)) (scal_u (snd (scal_reduce x n))).
Proof. rewrite ?gw_eq_scal_reduce, ?gw_eq_scal_u; first [GwInst.gw_exact (@QQRC.Mq2.m_scalbnl_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq2.m_scalbnl_eq)]. Qed.

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 112, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 112) q.
Lemma gw_eq_scalbnl_post : @scalbnl_post = ltac:(GwInst.gw_term (@QQRC.Mq2.scalbnl_post rsegs) (@scalbnl_post)). Proof. unfold scalbnl_post, QQRC.Mq2.scalbnl_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbnl_post : gw_eqs.

Definition scalbnl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
stk rsegs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
(-2^31 <= n < 2^31)%Z ->
mem_inv rsegs m ->
evt rsegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCALBNL) fc None m (seg_rom rsegs)).
Lemma gw_eq_scalbnl_stmt : @scalbnl_stmt = ltac:(GwInst.gw_term (@QQRC.Mq2.scalbnl_stmt rsegs 0x5d870) (@scalbnl_stmt)). Proof. unfold scalbnl_stmt, QQRC.Mq2.scalbnl_stmt; rewrite ?gw_eq_SCALBNL, ?gw_eq_scalbnl_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbnl_stmt : gw_eqs.

Lemma scalbnl_spec : scalbnl_stmt.
Proof. rewrite ?gw_eq_scalbnl_stmt; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq2.scalbnl_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq2.scalbnl_spec)]. Qed.

