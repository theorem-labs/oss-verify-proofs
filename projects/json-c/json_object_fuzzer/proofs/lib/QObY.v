(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiw1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiw1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiMA_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiMA_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0xd09b4 QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd09b4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd09b4 /\ 0xd09b4 + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition divtf3_mid2_pc := 0xd0d0c%Z.
Lemma gw_eq_divtf3_mid2_pc : @divtf3_mid2_pc = ltac:(GwInst.gw_term (@QDXD.divtf3_mid2_pc 0xd09b4) (@divtf3_mid2_pc)). Proof. unfold divtf3_mid2_pc, QDXD.divtf3_mid2_pc; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_divtf3_mid2_pc : gw_eqs.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. first [GwInst.gw_exact (@QDXD.ltb1_eqb0 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32) | autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.ltb1_eqb0 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32)]. Qed.

Definition divtf3_mid2 (sp gp tp w4 sgw w6 a6 : word) (F : bvmap 5 word) (fc : bv 32)
(ea eb aSigHi bSigHi scale x_hi x_lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi (bv_unsigned w4)) (E_A3 (bv_unsigned w4)) (E_A4 (bv_unsigned w4)) = (q_hi, q_lo)
/\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
/\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 0xd0d0c) fc None m (seg_rom rsegs).
Lemma gw_eq_divtf3_mid2 : @divtf3_mid2 = ltac:(GwInst.gw_term (@QDXD.divtf3_mid2 rsegs 0xd09b4) (@divtf3_mid2)). Proof. unfold divtf3_mid2, QDXD.divtf3_mid2; ltac2:(GwEq.gw_rw [[@gw_eq_E_A1__3; @gw_eq_E_A1__2; @gw_eq_E_A1]; [@gw_eq_E_A2__3; @gw_eq_E_A2__2; @gw_eq_E_A2]; [@gw_eq_E_A3__3; @gw_eq_E_A3__2; @gw_eq_E_A3]; [@gw_eq_E_A4__3; @gw_eq_E_A4__2; @gw_eq_E_A4]; [@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_divtf3_mid2 : gw_eqs.

Section Core2.
Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

#[using="Type"] Lemma divtf3_core2 : ltac2:(Q6nq.tyx '(@QDXD.divtf3_core2 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_E_A1__3; @gw_eq_E_A1__2; @gw_eq_E_A1]; [@gw_eq_E_A2__3; @gw_eq_E_A2__2; @gw_eq_E_A2]; [@gw_eq_E_A2sh__3; @gw_eq_E_A2sh__2; @gw_eq_E_A2sh]; [@gw_eq_E_A3__3; @gw_eq_E_A3__2; @gw_eq_E_A3]; [@gw_eq_E_A4__3; @gw_eq_E_A4__2; @gw_eq_E_A4]; [@gw_eq_E_X4__3; @gw_eq_E_X4__2; @gw_eq_E_X4]; [@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]; [@gw_eq_E_p3__3; @gw_eq_E_p3__2; @gw_eq_E_p3]; [@gw_eq_E_p42__3; @gw_eq_E_p42__2; @gw_eq_E_p42]; [@gw_eq_divtf3_mid2]; [@gw_eq_divtf3_mid2_pc__3; @gw_eq_divtf3_mid2_pc__2; @gw_eq_divtf3_mid2_pc]] '([(-1024); 1024; 32768; 854988]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_mid1_pc) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_divtf3_mid2; ltac2:(GwEq.gw_rw [[@gw_eq_E_A1__3; @gw_eq_E_A1__2; @gw_eq_E_A1]; [@gw_eq_E_A2__3; @gw_eq_E_A2__2; @gw_eq_E_A2]; [@gw_eq_E_A2sh__3; @gw_eq_E_A2sh__2; @gw_eq_E_A2sh]; [@gw_eq_E_A3__3; @gw_eq_E_A3__2; @gw_eq_E_A3]; [@gw_eq_E_A4__3; @gw_eq_E_A4__2; @gw_eq_E_A4]; [@gw_eq_E_X4__3; @gw_eq_E_X4__2; @gw_eq_E_X4]; [@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]; [@gw_eq_E_p3__3; @gw_eq_E_p3__2; @gw_eq_E_p3]; [@gw_eq_E_p42__3; @gw_eq_E_p42__2; @gw_eq_E_p42]]); first [GwInst.gw_exact (@QDXD.divtf3_core2 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32) | autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.divtf3_core2 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32)]. Qed.

Definition divtf3_midC (sp gp tp sgw a6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
(forall sgn, div_core sgn ea eb aSigHi aLo bSigHi bLo scale
= divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo))
/\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
/\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop aLo)) (Z_to_bv 64 (E_aHi2 aSigHi))
y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo aLo)) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 0xd0d0c) fc None m (seg_rom rsegs).
Lemma gw_eq_divtf3_midC : @divtf3_midC = ltac:(GwInst.gw_term (@QDXD.divtf3_midC rsegs 0xd09b4) (@divtf3_midC)). Proof. unfold divtf3_midC, QDXD.divtf3_midC; ltac2:(GwEq.gw_rw [[@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_divtf3_midC : gw_eqs.

#[using="Type"] Lemma divtf3_core12 : ltac2:(Q6nq.tyx '(@QDXD.divtf3_core12 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_divtf3_midC]; [@gw_eq_divtf3_mid2_pc__3; @gw_eq_divtf3_mid2_pc__2; @gw_eq_divtf3_mid2_pc]; [@gw_eq_divtf3_mid2__3; @gw_eq_divtf3_mid2__2; @gw_eq_divtf3_mid2]] '([(-1024); 1024; 32768; 854588]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_core_pc) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_divtf3_midC; first [GwInst.gw_exact (@QDXD.divtf3_core12 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32) | autorewrite with gw_eqs; GwInst.gw_exact (@QDXD.divtf3_core12 rsegs 0xd09b4 gw_code gw_base4 gw_baser mulhu_shl32)]. Qed.
End Core2.
Lemma gw_eq_divtf3_midC__2 : @divtf3_midC = ltac:(GwInst.gw_term (@QDXD.divtf3_midC rsegs 0xd09b4) (@divtf3_midC)). Proof. unfold divtf3_midC, QDXD.divtf3_midC; ltac2:(GwEq.gw_rw [[@gw_eq_E_a2Lo__3; @gw_eq_E_a2Lo__2; @gw_eq_E_a2Lo]; [@gw_eq_E_aHi2__3; @gw_eq_E_aHi2__2; @gw_eq_E_aHi2]; [@gw_eq_E_aLoTop__3; @gw_eq_E_aLoTop__2; @gw_eq_E_aLoTop]; [@gw_eq_E_aSigHiI__3; @gw_eq_E_aSigHiI__2; @gw_eq_E_aSigHiI]; [@gw_eq_E_bSigHiI__3; @gw_eq_E_bSigHiI__2; @gw_eq_E_bSigHiI]; [@gw_eq_E_expM1__3; @gw_eq_E_expM1__2; @gw_eq_E_expM1]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_divtf3_midC__2 : gw_eqs.
