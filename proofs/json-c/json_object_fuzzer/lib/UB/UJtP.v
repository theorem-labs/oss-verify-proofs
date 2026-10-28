(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Lemma gw_code : CodeAt.code_at rsegs 0x5958c QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5958c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5958c /\ 0x5958c + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition divtf3_core_pc := 0x59614%Z.
Lemma gw_eq_divtf3_core_pc : @divtf3_core_pc = ltac:(GwInst.gw_term (@QCa8.Mq1.divtf3_core_pc 0x5958c) (@divtf3_core_pc)). Proof. unfold divtf3_core_pc, QCa8.Mq1.divtf3_core_pc; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_core_pc : gw_eqs.
Definition divtf3_mid1_pc := 0x597a4%Z.
Lemma gw_eq_divtf3_mid1_pc : @divtf3_mid1_pc = ltac:(GwInst.gw_term (@QCa8.Mq1.divtf3_mid1_pc 0x5958c) (@divtf3_mid1_pc)). Proof. unfold divtf3_mid1_pc, QCa8.Mq1.divtf3_mid1_pc; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_mid1_pc : gw_eqs.

Lemma shl_shr_32 : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 32 = Z.land x 4294967295.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Mq1.shl_shr_32 rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

Definition E_aSigHiI (aSigHi : Z) := Z.lor aSigHi 281474976710656.
Lemma gw_eq_E_aSigHiI : @E_aSigHiI = ltac:(GwInst.gw_term (@QCa8.Mq1.E_aSigHiI) (@E_aSigHiI)). Proof. unfold E_aSigHiI, QCa8.Mq1.E_aSigHiI; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_aSigHiI : gw_eqs.
Definition E_bSigHiI (bSigHi : Z) := Z.lor bSigHi 281474976710656.
Lemma gw_eq_E_bSigHiI : @E_bSigHiI = ltac:(GwInst.gw_term (@QCa8.Mq1.E_bSigHiI) (@E_bSigHiI)). Proof. unfold E_bSigHiI, QCa8.Mq1.E_bSigHiI; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_bSigHiI : gw_eqs.
Definition E_aLoTop (aLo : Z) := Z.shiftr aLo 63.
Lemma gw_eq_E_aLoTop : @E_aLoTop = ltac:(GwInst.gw_term (@QCa8.Mq1.E_aLoTop) (@E_aLoTop)). Proof. unfold E_aLoTop, QCa8.Mq1.E_aLoTop; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_aLoTop : gw_eqs.
Definition E_a2Lo (aLo : Z) := Z.land (Z.shiftl aLo 1) 18446744073709551615.
Lemma gw_eq_E_a2Lo : @E_a2Lo = ltac:(GwInst.gw_term (@QCa8.Mq1.E_a2Lo) (@E_a2Lo)). Proof. unfold E_a2Lo, QCa8.Mq1.E_a2Lo; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_a2Lo : gw_eqs.
Definition E_aHi2n (aSigHi : Z) := Z.land (Z.shiftl aSigHi 1) 18446744073709551615.
Lemma gw_eq_E_aHi2n : @E_aHi2n = ltac:(GwInst.gw_term (@QCa8.Mq1.E_aHi2n) (@E_aHi2n)). Proof. unfold E_aHi2n, QCa8.Mq1.E_aHi2n; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_aHi2n : gw_eqs.
Definition E_aHi2 (aSigHi : Z) := Z.land (Z.shiftl (E_aSigHiI aSigHi) 1) 18446744073709551615.
Lemma gw_eq_E_aHi2 : @E_aHi2 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_aHi2) (@E_aHi2)). Proof. unfold E_aHi2, QCa8.Mq1.E_aHi2; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_aHi2 : gw_eqs.
Definition E_A1 (aSigHi : Z) := Z.shiftr (E_aHi2 aSigHi) 32.
Lemma gw_eq_E_A1 : @E_A1 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_A1) (@E_A1)). Proof. unfold E_A1, QCa8.Mq1.E_A1; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_A1 : gw_eqs.
Definition E_A2 (aSigHi aLo : Z) := Z.land (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 4294967295.
Lemma gw_eq_E_A2 : @E_A2 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_A2) (@E_A2)). Proof. unfold E_A2, QCa8.Mq1.E_A2; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_A2 : gw_eqs.
Definition E_A2sh (aSigHi aLo : Z) := Z.shiftl (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 32.
Lemma gw_eq_E_A2sh : @E_A2sh = ltac:(GwInst.gw_term (@QCa8.Mq1.E_A2sh) (@E_A2sh)). Proof. unfold E_A2sh, QCa8.Mq1.E_A2sh; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_A2sh : gw_eqs.
Definition E_A3 (aLo : Z) := Z.shiftr (E_a2Lo aLo) 32.
Lemma gw_eq_E_A3 : @E_A3 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_A3) (@E_A3)). Proof. unfold E_A3, QCa8.Mq1.E_A3; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_A3 : gw_eqs.
Definition E_A4 (aLo : Z) := Z.land (E_a2Lo aLo) 4294967294.
Lemma gw_eq_E_A4 : @E_A4 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_A4) (@E_A4)). Proof. unfold E_A4, QCa8.Mq1.E_A4; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_A4 : gw_eqs.
Definition E_X3 (x_lo : Z) := Z.shiftr x_lo 32.
Lemma gw_eq_E_X3 : @E_X3 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_X3) (@E_X3)). Proof. unfold E_X3, QCa8.Mq1.E_X3; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_X3 : gw_eqs.
Definition E_X4sh (x_lo : Z) := Z.land (Z.shiftl x_lo 32) 18446744073709551615.
Lemma gw_eq_E_X4sh : @E_X4sh = ltac:(GwInst.gw_term (@QCa8.Mq1.E_X4sh) (@E_X4sh)). Proof. unfold E_X4sh, QCa8.Mq1.E_X4sh; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_X4sh : gw_eqs.
Definition E_X4 (x_lo : Z) := Z.shiftr (E_X4sh x_lo) 32.
Lemma gw_eq_E_X4 : @E_X4 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_X4) (@E_X4)). Proof. unfold E_X4, QCa8.Mq1.E_X4; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_X4 : gw_eqs.
Definition E_p3 (x_lo A : Z) := Z.land (E_X3 x_lo * A) 18446744073709551615.
Lemma gw_eq_E_p3 : @E_p3 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_p3) (@E_p3)). Proof. unfold E_p3, QCa8.Mq1.E_p3; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_p3 : gw_eqs.
Definition E_p42 (x_lo aSigHi aLo : Z) := Z.land (E_X4 x_lo * E_A2 aSigHi aLo) 18446744073709551615.
Lemma gw_eq_E_p42 : @E_p42 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_p42) (@E_p42)). Proof. unfold E_p42, QCa8.Mq1.E_p42; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_p42 : gw_eqs.
Definition E_expM1 (scale ea eb : Z) := scale + 16382 + (ea - eb).
Lemma gw_eq_E_expM1 : @E_expM1 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_expM1) (@E_expM1)). Proof. unfold E_expM1, QCa8.Mq1.E_expM1; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_expM1 : gw_eqs.
Definition E_blo (bLo : Z) := Z.land (Z.shiftl bLo 15) 18446744073709551615.
Lemma gw_eq_E_blo : @E_blo = ltac:(GwInst.gw_term (@QCa8.Mq1.E_blo) (@E_blo)). Proof. unfold E_blo, QCa8.Mq1.E_blo; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_blo : gw_eqs.
Definition E_bhw (bSigHi bLo : Z) := Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl (E_bSigHiI bSigHi) 15) 18446744073709551615).
Lemma gw_eq_E_bhw : @E_bhw = ltac:(GwInst.gw_term (@QCa8.Mq1.E_bhw) (@E_bhw)). Proof. unfold E_bhw, QCa8.Mq1.E_bhw; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_bhw : gw_eqs.
Definition E_x0 (bSigHi bLo : Z) := Z.land (8432131802713292800 - E_bhw bSigHi bLo) 18446744073709551615.
Lemma gw_eq_E_x0 : @E_x0 = ltac:(GwInst.gw_term (@QCa8.Mq1.E_x0) (@E_x0)). Proof. unfold E_x0, QCa8.Mq1.E_x0; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_E_x0 : gw_eqs.

Definition DCW (sgn ea eb aSigHi aLo bSigHi bLo scale x_hi x_lo : Z) : Z :=
let '(q_hi, q_lo) := divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi aLo) (E_A3 aLo) (E_A4 aLo) in
divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo).
Lemma gw_eq_DCW : @DCW = ltac:(GwInst.gw_term (@QCa8.Mq1.DCW) (@DCW)). Proof. unfold DCW, QCa8.Mq1.DCW; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_DCW : gw_eqs.

Ltac half_block b_hw xp xn h corr lo hi r :=
zstep; model_reg 22 h (Z.shiftr (xp * b_hw) 64); mulhu_rng h;
zstep; model_reg 22 corr (Z.land (0 - h) 18446744073709551615);
zstep; model_reg 23 lo (Z.land (corr * xp) 18446744073709551615);
zstep; model_reg 21 hi (Z.shiftr (corr * xp) 64); mulhu_rng hi;
do 3 zstep; model_reg 21 r (Z.lor (Z.shiftr lo 63) (Z.land (Z.shiftl hi 1) 18446744073709551615));
replace (Z_to_bv 64 r) with (Z_to_bv 64 (half_iter xp b_hw)) by (f_equal; subst r hi lo corr h; reflexivity);
name_as xn (half_iter xp b_hw); hi_rng xn.

Definition divtf3_mid1 (ra sp gp tp w4 sgw w6 a5 a6 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(ea eb aSigHi bSigHi scale : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x_hi x_lo y21 y22,
(forall sgn, div_core sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale
= DCW sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale x_hi x_lo)
/\ (0 <= x_hi < 2^64)%Z /\ (0 <= x_lo < 2^64)%Z
/\ ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
(Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
(Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
(Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
(Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
F (Z_to_bv 64 0x597a4) fc None m (seg_rom rsegs).
Lemma gw_eq_divtf3_mid1 : @divtf3_mid1 = ltac:(GwInst.gw_term (@QCa8.Mq1.divtf3_mid1 rsegs 0x5958c) (@divtf3_mid1)). Proof. unfold divtf3_mid1, QCa8.Mq1.divtf3_mid1; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_divtf3_mid1 : gw_eqs.

Section Core1.
Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).

#[using="Type"] Lemma divtf3_core1 : ltac2:(Q6nq.tyx '(@QCa8.Mq1.divtf3_core1 rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_divtf3_core_pc__3; @gw_eq_divtf3_core_pc__2; @gw_eq_divtf3_core_pc]; [@gw_eq_divtf3_mid1_pc__3; @gw_eq_divtf3_mid1_pc__2; @gw_eq_divtf3_mid1_pc]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2n__3; @gw_eq_E_aHi2n__2; @gw_eq_E_aHi2n]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_A1__3; @gw_eq_E_A1__2; @gw_eq_E_A1]; [@gw_eq_E_A2__3; @gw_eq_E_A2__2; @gw_eq_E_A2]; [@gw_eq_E_A2sh__3; @gw_eq_E_A2sh__2; @gw_eq_E_A2sh]; [@gw_eq_E_A3__3; @gw_eq_E_A3__2; @gw_eq_E_A3]; [@gw_eq_E_A4__3; @gw_eq_E_A4__2; @gw_eq_E_A4]; [@gw_eq_E_X3__3; @gw_eq_E_X3__2; @gw_eq_E_X3]; [@gw_eq_E_X4sh__3; @gw_eq_E_X4sh__2; @gw_eq_E_X4sh]; [@gw_eq_E_X4__3; @gw_eq_E_X4__2; @gw_eq_E_X4]; [@gw_eq_E_p3__3; @gw_eq_E_p3__2; @gw_eq_E_p3]; [@gw_eq_E_p42__3; @gw_eq_E_p42__2; @gw_eq_E_p42]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]; [@gw_eq_E_blo__3; @gw_eq_E_blo__2; @gw_eq_E_blo]; [@gw_eq_E_bhw__3; @gw_eq_E_bhw__2; @gw_eq_E_bhw]; [@gw_eq_E_x0__3; @gw_eq_E_x0__2; @gw_eq_E_x0]; [@gw_eq_DCW__3; @gw_eq_DCW__2; @gw_eq_DCW]; [@gw_eq_divtf3_mid1__3; @gw_eq_divtf3_mid1__2; @gw_eq_divtf3_mid1]] '([(-1024); 1024; 32768; 366100]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_core_pc) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QCa8.Mq1.divtf3_core1 rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
End Core1.
