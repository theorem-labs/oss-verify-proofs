(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Lemma gw_code : CodeAt.code_at rsegs 0x582ac QQLG.multf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x582ac mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x582ac /\ 0x582ac + 1792 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition multf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 80) (bv_unsigned sp).
Lemma gw_eq_multf3_post : @multf3_post = ltac:(GwInst.gw_term (@Q91D.multf3_post rsegs) (@multf3_post)). Proof. unfold multf3_post, Q91D.multf3_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_multf3_post : gw_eqs.

Definition saved9 (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) (j : list byte) : list cell :=
[CB 8 j; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].
Lemma gw_eq_saved9 : @saved9 = ltac:(GwInst.gw_term (@Q91D.saved9) (@saved9)). Proof. unfold saved9, Q91D.saved9; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_saved9 : gw_eqs.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.land_M32_small rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma land_ones_r : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.land_ones_r rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.land_ones_l rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Lemma sra63_neg : forall x, -2^63 <= x < 0 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.sra63_neg rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma sra63_negw : forall x, 2^63 <= x < 2^64 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.sra63_negw rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma sra63_pos : forall x, 0 <= x < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.sra63_pos rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.lxor_b2z_1 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Ltac zzr := zsimp; rewrite ?Z.add_0_r;
try rewrite !land_sub_neg by alia;
try rewrite !land_M32_small by alia;
try rewrite !sra63_neg by alia; try rewrite !sra63_pos by alia;
try rewrite !land_ones_l by (first [zrange | alia]);
rewrite ?Z.land_0_l.
Ltac zrstep := step; zzr.

Lemma mfr_normal : ltac2:(Q6nq.tyx '(@Q91D.mfr_normal rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([131072; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.mfr_normal rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Lemma mfr_caseA : ltac2:(Q6nq.tyx '(@Q91D.mfr_caseA rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-126); 127; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.mfr_caseA rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Lemma mfr_caseB : ltac2:(Q6nq.tyx '(@Q91D.mfr_caseB rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([127; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.mfr_caseB rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Lemma mfr_caseC : ltac2:(Q6nq.tyx '(@Q91D.mfr_caseC rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([127; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.mfr_caseC rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Section Walk.
Variables (sp : word).

#[using="Type"] Lemma Lepi : ltac2:(Q6nq.tyx '(@Q91D.Lepi rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]; [@gw_eq_w0__3; @gw_eq_w0__2; @gw_eq_w0]] '([(-80); 4096; 362568]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Lepi rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Linf : ltac2:(Q6nq.tyx '(@Q91D.Linf rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361832; 9223090561878065152]%Z : list Z) '(Q6nq.gwt_unf (@INF_HI) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Linf rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lup : ltac2:(Q6nq.tyx '(@Q91D.Lup rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 362556; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Lup rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Ltie : ltac2:(Q6nq.tyx '(@Q91D.Ltie rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361900; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Ltie rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lrnd2 : ltac2:(Q6nq.tyx '(@Q91D.Lrnd2 rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 361884; 9223372036854775808]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Lrnd2 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lhalf : ltac2:(Q6nq.tyx '(@Q91D.Lhalf rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-80); 4096; 362544; 9223372036854775808]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Lhalf rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Lfin : ltac2:(Q6nq.tyx '(@Q91D.Lfin rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-131072); (-16383); (-80); 4096; 32767; 361852; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Lfin rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma Ltail : ltac2:(Q6nq.tyx '(@Q91D.Ltail rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-16383); (-1024); (-80); 1024; 4096; 65536; 361656; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@multf3_mid_pc) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil))))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Ltail rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
End Walk.

Lemma multf3_core : ltac2:(Q6nq.tyx '(@Q91D.multf3_core rsegs 0x582ac gw_code gw_base4 gw_baser) [[@gw_eq_multf3_post__3; @gw_eq_multf3_post__2; @gw_eq_multf3_post]; [@gw_eq_saved9__3; @gw_eq_saved9__2; @gw_eq_saved9]] '([(-1024); (-80); 1024; 4096; 32768; 361260; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@multf3_core_pc) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil))))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.multf3_core rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
