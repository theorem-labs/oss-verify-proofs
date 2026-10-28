(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFHW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFHW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umo7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umo7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ2O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ2O. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UHhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UHhK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UL4p. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWCD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWCD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UnyT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UnyT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOwl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOwl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGEX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGEX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGbx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGbx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXjc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXjc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZtE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZtE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBmb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBmb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition e_extenddftf2 := 0x57e74%Z.
Definition e_signbitl := 0x58004%Z.
Definition e_fpclassifyl := 0x5800c%Z.
Definition e_frexpl := 0x58050%Z.
Definition e_letf2 := 0x58128%Z.
Definition e_multf3 := 0x582ac%Z.
Definition e_floatsitf := 0x589ac%Z.
Definition e_subtf3 := 0x58b4c%Z.
Definition e_addtf3 := 0x58b5c%Z.
Definition e_fixunstfsi := 0x59364%Z.
Definition e_floatunsitf := 0x593f8%Z.
Definition e_divtf3 := 0x5958c%Z.
Definition letf2_spec := @letf2_spec.
Definition fixunstfsi_spec := @fixunstfsi_spec.
Definition floatsitf_spec := @floatsitf_spec.
Definition floatunsitf_spec := @floatunsitf_spec.
Definition extenddftf2_spec := @extenddftf2_spec.
Definition addtf3_spec := @addtf3_spec.
Definition subtf3_spec := @subtf3_spec.
Definition multf3_spec := @multf3_spec.
Definition frexpl_spec := @frexpl_spec.
Definition signbitl_spec := @signbitl_spec.
Definition fpclassifyl_spec := @fpclassifyl_spec.
End GwI.

Ltac norm_rsegs :=
cbv delta [rsegs rsegs rsegs rsegs rsegs rsegs
rsegs rsegs rsegs rsegs rsegs rsegs] in *;
fold rsegs in *.

Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.lo64_range). Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.hi64_range). Qed.

Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.
Lemma gw_eq_canon : @canon = ltac:(GwInst.gw_term (@Qy8Z.Mq0.canon) (@canon)). Proof. unfold canon, Qy8Z.Mq0.canon; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_canon : gw_eqs.

Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.lo64_canon). Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.hi64_canon). Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.mk128_canon). Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.canon_small). Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.canon_range). Qed.

Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_mul_canon). Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_div_canon). Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_add_canon). Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_add_canon_l). Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_sub_canon). Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.f128_le_canon). Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.fixunstfsi_a0_canon). Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.ulit_lo64). Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.ulit_hi64). Qed.

Local Open Scope bv_scope.

Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_leaf2_post : @leaf2_post = ltac:(GwInst.gw_term (@Qy8Z.Mq0.leaf2_post rsegs) (@leaf2_post)). Proof. unfold leaf2_post, Qy8Z.Mq0.leaf2_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_leaf2_post : gw_eqs.

Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_leaf1_post : @leaf1_post = ltac:(GwInst.gw_term (@Qy8Z.Mq0.leaf1_post rsegs) (@leaf1_post)). Proof. unfold leaf1_post, Qy8Z.Mq0.leaf1_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_leaf1_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qy8Z.Mq0.divtf3_stmt) (@UB5o.divtf3_stmt) (Q6nq.gwt_def (@QVbl.divtf3_stmt) (@UB5o.divtf3_stmt) Q6nq.gwt_nil)).
Lemma letf2_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.letf2_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([360744]%Z : list Z) '(Q6nq.gwt_unf (@letf2_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.letf2_callv). Qed.

Lemma letf2_callv0 : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.letf2_callv0) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([360744]%Z : list Z) '(Q6nq.gwt_unf (@letf2_entry) (Q6nq.gwt_zc F128_ZERO gwt_X))).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.letf2_callv0). Qed.

Lemma fixunstfsi_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.fixunstfsi_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([365412]%Z : list Z) '(Q6nq.gwt_unf (@fixunstfsi_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.fixunstfsi_callv). Qed.

Lemma floatsitf_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.floatsitf_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([362924]%Z : list Z) '(Q6nq.gwt_unf (@floatsitf_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.floatsitf_callv). Qed.

Lemma floatsitf_callp : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.floatsitf_callp) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([362924]%Z : list Z) '(Q6nq.gwt_unf (@floatsitf_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.floatsitf_callp). Qed.

Lemma floatunsitf_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.floatunsitf_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([365560]%Z : list Z) '(Q6nq.gwt_unf (@floatunsitf_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.floatunsitf_callv). Qed.

Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.sext32_idem). Qed.
Lemma floatunsitf_callfix : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.floatunsitf_callfix) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]] '([365560]%Z : list Z) '(Q6nq.gwt_unf (@floatunsitf_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.floatunsitf_callfix). Qed.

Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
mem_inv rsegs m -> (0 <= D < 2^64)%Z ->
evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 0x57e74) fc None m (seg_rom rsegs)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.extenddftf2_callv). Qed.

Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - K, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - K) q.
Lemma gw_eq_call2_post : @call2_post = ltac:(GwInst.gw_term (@Qy8Z.Mq0.call2_post rsegs) (@call2_post)). Proof. unfold call2_post, Qy8Z.Mq0.call2_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_call2_post : gw_eqs.

Lemma multf3_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.multf3_callq) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]] '([(-80); 80; 4096; 361132]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.multf3_callq). Qed.

Lemma divtf3_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.divtf3_callq) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_divtf3_stmt__3; @gw_eq_divtf3_stmt__2; @gw_eq_divtf3_stmt]] '([(-112); 112; 4096; 365964]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.divtf3_callq). Qed.

Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(q - 48, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ stk rsegs m' (q - 48) q.
Lemma gw_eq_calla_post : @calla_post = ltac:(GwInst.gw_term (@Qy8Z.Mq0.calla_post rsegs) (@calla_post)). Proof. unfold calla_post, Qy8Z.Mq0.calla_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_calla_post : gw_eqs.

Lemma addtf3_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.addtf3_callq) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]] '([363356]%Z : list Z) '(Q6nq.gwt_unf (@addtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.addtf3_callq). Qed.

Lemma subtf3_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.subtf3_callq) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]] '([363340]%Z : list Z) '(Q6nq.gwt_unf (@subtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.subtf3_callq). Qed.

Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 32) q
/\ rw_cells rsegs m' P (C4 (Z_to_bv 64 e') :: rest)
/\ frexpl FREXPL_FUEL x E = Some (x', e').
Lemma gw_eq_frexpl_postq : @frexpl_postq = ltac:(GwInst.gw_term (@Qy8Z.Mq0.frexpl_postq rsegs) (@frexpl_postq)). Proof. unfold frexpl_postq, Qy8Z.Mq0.frexpl_postq; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_frexpl_postq : gw_eqs.

Lemma frexpl_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.frexpl_callq) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]; [@gw_eq_frexpl_postq__3; @gw_eq_frexpl_postq__2; @gw_eq_frexpl_postq]] '([32767; 360528]%Z : list Z) '(Q6nq.gwt_unf (@frexpl_entry) (Q6nq.gwt_zc F128_ZERO gwt_X))).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.frexpl_callq). Qed.

Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.signbitl_canon). Qed.
Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.fpclassifyl_canon). Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_signbitl_postv : @signbitl_postv = ltac:(GwInst.gw_term (@Qy8Z.Mq0.signbitl_postv rsegs) (@signbitl_postv)). Proof. unfold signbitl_postv, Qy8Z.Mq0.signbitl_postv; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_signbitl_postv : gw_eqs.
Lemma signbitl_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.signbitl_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]; [@gw_eq_frexpl_postq__3; @gw_eq_frexpl_postq__2; @gw_eq_frexpl_postq]; [@gw_eq_signbitl_postv__3; @gw_eq_signbitl_postv__2; @gw_eq_signbitl_postv]] '([360452]%Z : list Z) '(Q6nq.gwt_unf (@signbitl_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.signbitl_callv). Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_fpclassifyl_postv : @fpclassifyl_postv = ltac:(GwInst.gw_term (@Qy8Z.Mq0.fpclassifyl_postv rsegs) (@fpclassifyl_postv)). Proof. unfold fpclassifyl_postv, Qy8Z.Mq0.fpclassifyl_postv; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fpclassifyl_postv : gw_eqs.
Lemma fpclassifyl_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Qy8Z.Mq0.fpclassifyl_callv) [[@gw_eq_canon__3; @gw_eq_canon__2; @gw_eq_canon]; [@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]; [@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]; [@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]; [@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]; [@gw_eq_frexpl_postq__3; @gw_eq_frexpl_postq__2; @gw_eq_frexpl_postq]; [@gw_eq_signbitl_postv__3; @gw_eq_signbitl_postv__2; @gw_eq_signbitl_postv]; [@gw_eq_fpclassifyl_postv__3; @gw_eq_fpclassifyl_postv__2; @gw_eq_fpclassifyl_postv]] '([360460]%Z : list Z) '(Q6nq.gwt_unf (@fpclassifyl_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Qy8Z.Mq0.fpclassifyl_callv). Qed.

Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.lo64_flip_sign). Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.Mq0.hi64_flip_sign). Qed.
