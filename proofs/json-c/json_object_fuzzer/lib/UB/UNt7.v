(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGbx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGbx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4WT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4WT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFHW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFHW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ2O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ2O. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBmb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBmb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UL4p. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqYW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqYW.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Definition e_fpclassifyl := 0x5800c%Z.
Definition e_letf2 := 0x58128%Z.
Definition e_multf3 := 0x582ac%Z.
Definition e_floatsitf := 0x589ac%Z.
Definition e_divtf3 := 0x5958c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5d870 (Q8l1.Mq0.fmodlblk_code 0xf79fa0ef%Z 0xee0fa0ef%Z 0x84dfa0ef%Z 0xb21fb0ef%Z 0xd64fa0ef%Z 0xe40fa0ef%Z 0xe28fa0ef%Z 0xf70fa0ef%Z 0xed8fa0ef%Z 0xd99fa0ef%Z 0xe8cfa0ef%Z 0xde4fa0ef%Z 0xda0fa0ef%Z 0xd88fa0ef%Z 0xd44fa0ef%Z 0xd2cfa0ef%Z 0xfffb5517%Z 0x61453507%Z 0x890fa0ef%Z 0xc9cfa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5d870 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5d870 /\ 0x5d870 + 1468 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition divtf3_spec := @divtf3_spec.
Definition fpclassifyl_spec := @fpclassifyl_spec.
Definition letf2_spec := @letf2_spec.
Definition floatsitf_spec := @floatsitf_spec.
Definition multf3_spec := @multf3_spec.
Lemma D_233 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @D_233). Proof. GwApply.gw_side. Qed.
Lemma E_233 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @E_233). Proof. GwApply.gw_side. Qed.
Lemma D_236 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @D_236). Proof. GwApply.gw_side. Qed.
Lemma E_236 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @E_236). Proof. GwApply.gw_side. Qed.
Lemma D_278 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @D_278). Proof. GwApply.gw_side. Qed.
Lemma E_278 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @E_278). Proof. GwApply.gw_side. Qed.
Lemma LINK_233 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @LINK_233). Proof. GwApply.gw_side. Qed.
Lemma LINK_236 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @LINK_236). Proof. GwApply.gw_side. Qed.
Lemma LINK_278 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mq0.gw_all) @LINK_278). Proof. GwApply.gw_side. Qed.
End GwI.

Definition FMODL : Z := 0x5d9f4.
Lemma gw_eq_FMODL : @FMODL = ltac:(GwInst.gw_term (@Q8l1.Mq0.FMODL 0x5d870) (@FMODL)). Proof. unfold FMODL, Q8l1.Mq0.FMODL; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMODL : gw_eqs.
Definition RFMODL_DEPTH : Z := 192.
Lemma gw_eq_RFMODL_DEPTH : @RFMODL_DEPTH = ltac:(GwInst.gw_term (@Q8l1.Mq0.RFMODL_DEPTH) (@RFMODL_DEPTH)). Proof. unfold RFMODL_DEPTH, Q8l1.Mq0.RFMODL_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RFMODL_DEPTH : gw_eqs.

Ltac lit_loads :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in (bv_swrap 32 (c mod 2^64))%Z in
let c'' := eval vm_compute in (c' mod 2^64)%Z in
replace (sx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c'') by (unfold sx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
| |- context [zx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in ((c mod 2^64) mod 2^32)%Z in
replace (zx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c') by (unfold zx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
end.

Definition extsf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma gw_eq_extsf_post : @extsf_post = ltac:(GwInst.gw_term (@Q8l1.Mq0.extsf_post rsegs) (@extsf_post)). Proof. unfold extsf_post, Q8l1.Mq0.extsf_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_extsf_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QCa8.multf3_stmt) (@UGbx.multf3_stmt) (Q6nq.gwt_def (@Q8l1.Mq0.multf3_stmt) (@UGbx.multf3_stmt) (Q6nq.gwt_def (@Q91D.multf3_post) (@Uwbh.multf3_post) (Q6nq.gwt_def (@Q8l1.Mq0.multf3_post) (@Uwbh.multf3_post) (Q6nq.gwt_def (@QVbl.Mq2.letf2_post) (@UFHW.letf2_post) (Q6nq.gwt_def (@Q8l1.Mq0.letf2_post) (@UFHW.letf2_post) (Q6nq.gwt_def (@Qy8Z.Mq0.leaf2_post) (@UuJ9.leaf2_post) (Q6nq.gwt_def (@Q8l1.Mq0.leaf2_post) (@UuJ9.leaf2_post) (Q6nq.gwt_def (@Qy8Z.Mq0.leaf1_post) (@UuJ9.leaf1_post) (Q6nq.gwt_def (@Q8l1.Mq0.leaf1_post) (@UuJ9.leaf1_post) (Q6nq.gwt_def (@QQLG.Mq5.fpclassifyl_post) (@UBmb.fpclassifyl_post) (Q6nq.gwt_def (@Q8l1.Mq0.fpclassifyl_post) (@UBmb.fpclassifyl_post) (Q6nq.gwt_def (@Q8l1.Mq0.floatsitf_post) (@UJ2O.floatsitf_post) (Q6nq.gwt_def (@QQLG.Mq3.floatsitf_post) (@UJ2O.floatsitf_post) (Q6nq.gwt_def (@Q8l1.Mq0.extenddftf2_post) (@UL4p.extenddftf2_post) (Q6nq.gwt_def (@QQLG.Mq1.extenddftf2_post) (@UL4p.extenddftf2_post) (Q6nq.gwt_def (@Q8l1.Mq0.divtf3_stmt) (@UB5o.divtf3_stmt) (Q6nq.gwt_def (@QVbl.divtf3_stmt) (@UB5o.divtf3_stmt) (Q6nq.gwt_def (@Q8l1.Mq0.divtf3_post) (@UB5o.divtf3_post) (Q6nq.gwt_def (@QVbl.divtf3_post) (@UB5o.divtf3_post) (Q6nq.gwt_def (@Qy8Z.Mq0.call2_post) (@UuJ9.call2_post) (Q6nq.gwt_def (@Q8l1.Mq0.call2_post) (@UuJ9.call2_post) Q6nq.gwt_nil)))))))))))))))))))))).
Lemma extendsftf2_2p120 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.extendsftf2_2p120) [[@gw_eq_extsf_post]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]] '([383088; 18446744071486570496]%Z : list Z) '(Q6nq.gwt_zc C_2P120 gwt_X)).
Proof. rewrite ?gw_eq_extsf_post; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.extendsftf2_2p120) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.extendsftf2_2p120)]. Qed.

Lemma extendsftf2_2pm120 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.extendsftf2_2pm120) [[@gw_eq_extsf_post]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]] '([383088; 18446744069473304576]%Z : list Z) '(Q6nq.gwt_zc C_2PM120 gwt_X)).
Proof. rewrite ?gw_eq_extsf_post; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.extendsftf2_2pm120) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.extendsftf2_2pm120)]. Qed.

Lemma m_fpclassifyl_canon : forall y, fpclassifyl (lo64 y + 2^64 * hi64 y) = m_fpclassifyl y.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.m_fpclassifyl_canon) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.m_fpclassifyl_canon)]. Qed.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - RFMODL_DEPTH) q
/\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).
Lemma gw_eq_rfmodl_post : @rfmodl_post = ltac:(GwInst.gw_term (@Q8l1.Mq0.rfmodl_post rsegs) (@rfmodl_post)). Proof. unfold rfmodl_post, Q8l1.Mq0.rfmodl_post; rewrite ?gw_eq_RFMODL_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rfmodl_post : gw_eqs.

Definition rfmodl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
stk rsegs m (q - RFMODL_DEPTH) q -> mem_inv rsegs m ->
(4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
m_fmodl X Y = Some r ->
evt rsegs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom rsegs)).
Lemma gw_eq_rfmodl_stmt : @rfmodl_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq0.rfmodl_stmt rsegs 0x5d870) (@rfmodl_stmt)). Proof. unfold rfmodl_stmt, Q8l1.Mq0.rfmodl_stmt; rewrite ?gw_eq_FMODL, ?gw_eq_RFMODL_DEPTH, ?gw_eq_rfmodl_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rfmodl_stmt : gw_eqs.

Section Fmodl.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (X Y r : Z).
Hypothesis SPLO : (4096 <= q - RFMODL_DEPTH)%Z.
Hypothesis SPHI : (q < 2^63)%Z.
Hypothesis HM : m_fmodl X Y = Some r.

Definition frame : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma gw_eq_frame : @frame = ltac:(GwInst.gw_term (@Q8l1.Mq0.frame) (@frame)). Proof. unfold frame, Q8l1.Mq0.frame; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_frame : gw_eqs.

Definition finv (m : word -> option byte) : Prop :=
mem_inv rsegs m /\ munch [(q - RFMODL_DEPTH, q)]%Z m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -80) frame /\ stk rsegs m (q - RFMODL_DEPTH) (q + -80).
Lemma gw_eq_finv : @finv = ltac:(GwInst.gw_term (@Q8l1.Mq0.finv rsegs) (@finv)). Proof. unfold finv, Q8l1.Mq0.finv; rewrite ?gw_eq_RFMODL_DEPTH, ?gw_eq_frame; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_finv : gw_eqs.

Definition Fok (F' : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k.
Lemma gw_eq_Fok : @Fok = ltac:(GwInst.gw_term (@Q8l1.Mq0.Fok) (@Fok)). Proof. unfold Fok, Q8l1.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_Fok : gw_eqs.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.Fok_refl) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.Fok_refl)]. Qed.
#[using="Type"] Lemma Fok_set10 : forall F' v, Fok F' -> Fok (bvmap_set 10 v F').
Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.Fok_set10) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.Fok_set10)]. Qed.

Definition exv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x7fff.
Lemma gw_eq_exv : @exv = ltac:(GwInst.gw_term (@Q8l1.Mq0.exv) (@exv)). Proof. unfold exv, Q8l1.Mq0.exv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_exv : gw_eqs.
Definition eyv : Z := Z.land (Z.shiftr (hi64 Y) 48) 0x7fff.
Lemma gw_eq_eyv : @eyv = ltac:(GwInst.gw_term (@Q8l1.Mq0.eyv) (@eyv)). Proof. unfold eyv, Q8l1.Mq0.eyv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_eyv : gw_eqs.
Definition sxv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x8000.
Lemma gw_eq_sxv : @sxv = ltac:(GwInst.gw_term (@Q8l1.Mq0.sxv) (@sxv)). Proof. unfold sxv, Q8l1.Mq0.sxv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_sxv : gw_eqs.

#[using="Type"] Lemma L_ret : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_ret) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([383600]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_ret) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_ret)]. Qed.

Definition DS : divtf3_stmt := U4WT.divtf3_spec.
#[using="Type"] Lemma stk_lower : forall m lo lo' hi, stk rsegs m lo hi -> (lo <= lo' <= hi)%Z -> stk rsegs m lo' hi.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.stk_lower) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.stk_lower)]. Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 192)%Z (q + -80)%Z |- _ =>
let ST1 := fresh "ST1" in let ST2 := fresh "ST2" in
destruct (stk_split _ _ _ (q + -80 - K)%Z _ ST ltac:(lia)) as [ST1 ST2]; clear ST;
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -80 - K)%Z (q + -80)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1 STn ltac:(lia)) as ST; clear ST1 STn end
end.

#[using="SPLO SPHI"] Lemma L_nan : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_nan) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([383568]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_nan) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_nan)]. Qed.

#[using="SPLO SPHI"] Lemma L_zero : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_zero) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([384020]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_zero) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_zero)]. Qed.

#[using="Type"] Lemma L_retx : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_retx) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([384132]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_retx) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_retx)]. Qed.

#[using="Type"] Lemma sxv_cases : sxv = 0%Z \/ sxv = 32768%Z.
Proof. rewrite ?gw_eq_sxv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.sxv_cases) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.sxv_cases)]. Qed.
#[using="Type"] Lemma sext_field : forall e, Z.land (Z.lor (Z.land e 65535) sxv) 65535 = Z.land (Z.lor e sxv) 65535.
Proof. rewrite ?gw_eq_sxv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.sext_field) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.sext_field)]. Qed.
#[using="Type"] Lemma exv_range : (0 <= exv < 32768)%Z.
Proof. rewrite ?gw_eq_exv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.exv_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.exv_range)]. Qed.
#[using="Type"] Lemma eyv_range : (0 <= eyv < 32768)%Z.
Proof. rewrite ?gw_eq_eyv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.eyv_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.eyv_range)]. Qed.
#[using="Type"] Lemma shr48X : Z.shiftr (hi64 X) 48 = (hi64 X / 2^48)%Z. Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.shr48X) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.shr48X)]. Qed.

#[using="Type"] Lemma land_M_16 : forall e, Z.land (Z.land e 18446744073709551615) 65535 = Z.land e 65535.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.land_M_16) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.land_M_16)]. Qed.

#[using="Type"] Lemma pack_bridge : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.pack_bridge) [[@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([65535; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X))))).
Proof. rewrite ?gw_eq_sxv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.pack_bridge) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.pack_bridge)]. Qed.
#[using="Type"] Lemma pack_bridge_lo : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.pack_bridge_lo) [[@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([65535; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X))).
Proof. rewrite ?gw_eq_sxv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.pack_bridge_lo) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.pack_bridge_lo)]. Qed.

#[using="SPLO SPHI"] Lemma L_scale : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_scale) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([32768; 384084]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_scale) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_scale)]. Qed.

#[using="SPLO SPHI"] Lemma L_L2 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_L2) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([32768; 384056]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_L2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_L2)]. Qed.

#[using="SPLO SPHI"] Lemma L_K2 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_K2) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([384044]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_K2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_K2)]. Qed.

#[using="SPLO SPHI"] Lemma L_fin : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_fin) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([383988]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_fin) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_fin)]. Qed.

#[using="Type"] Lemma dbl_bridge : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.dbl_bridge) [[@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)))).
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.dbl_bridge) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.dbl_bridge)]. Qed.
#[using="Type"] Lemma shr63_b : forall l, (0 <= l < 2^64)%Z -> (0 <= Z.shiftr l 63 <= 1)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.shr63_b) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.shr63_b)]. Qed.
#[using="Type"] Lemma u64_range : forall v, (0 <= u64 v < 2^64)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.u64_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.u64_range)]. Qed.
#[using="Type"] Lemma zbv_shl1 : forall v, Z_to_bv 64 (Z.shiftl v 1) = Z_to_bv 64 (u64 (2 * v)).
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.zbv_shl1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.zbv_shl1)]. Qed.

#[using="SPLO SPHI"] Lemma L_L1 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_L1) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([383884]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_L1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_L1)]. Qed.

#[using="Type"] Lemma ex_field : forall v, (0 <= v < 2^16)%Z -> Z.shiftr (Z.land (Z.shiftl v 49) 18446744073709551615) 49 = Z.land v 32767.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.ex_field) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.ex_field)]. Qed.
#[using="Type"] Lemma mant_or_range : forall h, (0 <= Z.lor (Z.land h 281474976710655) 281474976710656 < 2^64)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.mant_or_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.mant_or_range)]. Qed.

#[using="SPLO SPHI"] Lemma L_setup : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_setup) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_sxv]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]] '([383824; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X))).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_sxv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_setup) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_setup)]. Qed.

Definition UX : Z := mk128 (Z.land (hi64 X) 0x7fffffffffffffff) (lo64 X).
Lemma gw_eq_UX : @UX = ltac:(GwInst.gw_term (@Q8l1.Mq0.UX) (@UX)). Proof. unfold UX, Q8l1.Mq0.UX; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_UX : gw_eqs.
Definition UY : Z := mk128 (Z.land (hi64 Y) 0x7fffffffffffffff) (lo64 Y).
Lemma gw_eq_UY : @UY = ltac:(GwInst.gw_term (@Q8l1.Mq0.UY) (@UY)). Proof. unfold UY, Q8l1.Mq0.UY; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_UY : gw_eqs.
#[using="Type"] Lemma UX_words : lo64 UX = lo64 X /\ hi64 UX = Z.land (hi64 X) 0x7fffffffffffffff.
Proof. rewrite ?gw_eq_UX; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.UX_words) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.UX_words)]. Qed.
#[using="Type"] Lemma UY_words : lo64 UY = lo64 Y /\ hi64 UY = Z.land (hi64 Y) 0x7fffffffffffffff.
Proof. rewrite ?gw_eq_UY; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.UY_words) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.UY_words)]. Qed.

Definition K_normy (ux ex uy ey : Z) : option Z :=
(let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X yhi (lo64 uy) ey (xhi, lo64 ux, ex) with
| Some res => fmodl_K1 X yhi (lo64 uy) sxv res
| None => None end)%Z.
Lemma gw_eq_K_normy : @K_normy = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_normy) (@K_normy)). Proof. unfold K_normy, Q8l1.Mq0.K_normy; rewrite ?gw_eq_sxv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_K_normy : gw_eqs.

#[using="SPLO SPHI"] Lemma L_normy : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_normy) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_UY]; [@gw_eq_K_normy]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]; [@gw_eq_UX__3; @gw_eq_UX__2; @gw_eq_UX]] '([(-120); 383776]%Z : list Z) '(Q6nq.gwt_zc C_2P120 (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X))).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_UY, ?gw_eq_K_normy; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_normy) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_normy)]. Qed.

#[using="SPLO SPHI"] Lemma L_norm : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_norm) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_Fok]; [@gw_eq_exv]; [@gw_eq_eyv]; [@gw_eq_UX]; [@gw_eq_UY]; [@gw_eq_K_normy]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([(-120); 383756; 9223372036854775807]%Z : list Z) '(Q6nq.gwt_unf (@INTMAX_MAX) (Q6nq.gwt_unf (@ABS_HI) (Q6nq.gwt_zc C_2P120 (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X))))).
Proof. rewrite ?gw_eq_finv, ?gw_eq_Fok, ?gw_eq_exv, ?gw_eq_eyv, ?gw_eq_UX, ?gw_eq_UY, ?gw_eq_K_normy; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_norm) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_norm)]. Qed.

Definition K_norm : option Z :=
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey).
Lemma gw_eq_K_norm : @K_norm = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_norm) (@K_norm)). Proof. unfold K_norm, Q8l1.Mq0.K_norm; rewrite ?gw_eq_exv, ?gw_eq_eyv, ?gw_eq_UX, ?gw_eq_UY, ?gw_eq_K_normy; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_K_norm : gw_eqs.
Definition K_cmp : option Z :=
if f128_le UX UY <=? 0 then (if f128_le UX UY =? 0 then Some (f128_mul (f128_of_i32 0) X) else Some X) else K_norm.
Lemma gw_eq_K_cmp : @K_cmp = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_cmp) (@K_cmp)). Proof. unfold K_cmp, Q8l1.Mq0.K_cmp; rewrite ?gw_eq_UX, ?gw_eq_UY, ?gw_eq_K_norm; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_K_cmp : gw_eqs.

#[using="SPLO SPHI"] Lemma L_cmp : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_cmp) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_finv]; [@gw_eq_exv]; [@gw_eq_K_cmp]; [@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH__3; @gw_eq_RFMODL_DEPTH__2; @gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]; [@gw_eq_UX__3; @gw_eq_UX__2; @gw_eq_UX]; [@gw_eq_UY__3; @gw_eq_UY__2; @gw_eq_UY]; [@gw_eq_K_normy__3; @gw_eq_K_normy__2; @gw_eq_K_normy]; [@gw_eq_K_norm__3; @gw_eq_K_norm__2; @gw_eq_K_norm]] '([32767; 383664]%Z : list Z) '(Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_exv, ?gw_eq_K_cmp; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_cmp) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_cmp)]. Qed.

#[using="SPLO SPHI HM"] Lemma L_entry : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq0.L_entry) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_FMODL]; [@gw_eq_RFMODL_DEPTH]; [@gw_eq_extsf_post__3; @gw_eq_extsf_post__2; @gw_eq_extsf_post]; [@gw_eq_rfmodl_post__3; @gw_eq_rfmodl_post__2; @gw_eq_rfmodl_post]; [@gw_eq_rfmodl_stmt__3; @gw_eq_rfmodl_stmt__2; @gw_eq_rfmodl_stmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_exv__3; @gw_eq_exv__2; @gw_eq_exv]; [@gw_eq_eyv__3; @gw_eq_eyv__2; @gw_eq_eyv]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]; [@gw_eq_UX__3; @gw_eq_UX__2; @gw_eq_UX]; [@gw_eq_UY__3; @gw_eq_UY__2; @gw_eq_UY]; [@gw_eq_K_normy__3; @gw_eq_K_normy__2; @gw_eq_K_normy]; [@gw_eq_K_norm__3; @gw_eq_K_norm__2; @gw_eq_K_norm]; [@gw_eq_K_cmp__3; @gw_eq_K_cmp__2; @gw_eq_K_cmp]] '(@nil Z) '(Q6nq.gwt_zc RFMODL_DEPTH (Q6nq.gwt_zc FMODL (Q6nq.gwt_def (@Q8l1.Mq0.DS) (@DS) gwt_X)))).
Proof. rewrite ?gw_eq_FMODL, ?gw_eq_RFMODL_DEPTH; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_entry) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.L_entry)]. Qed.
End Fmodl.
Lemma gw_eq_frame__2 : @frame = ltac:(GwInst.gw_term (@Q8l1.Mq0.frame) (@frame)). Proof. unfold frame, Q8l1.Mq0.frame; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_frame__2 : gw_eqs.
Lemma gw_eq_finv__2 : @finv = ltac:(GwInst.gw_term (@Q8l1.Mq0.finv rsegs) (@finv)). Proof. unfold finv, Q8l1.Mq0.finv; rewrite ?gw_eq_RFMODL_DEPTH, ?gw_eq_frame__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_finv__2 : gw_eqs.
Lemma gw_eq_Fok__2 : @Fok = ltac:(GwInst.gw_term (@Q8l1.Mq0.Fok) (@Fok)). Proof. unfold Fok, Q8l1.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_Fok__2 : gw_eqs.
Lemma gw_eq_exv__2 : @exv = ltac:(GwInst.gw_term (@Q8l1.Mq0.exv) (@exv)). Proof. unfold exv, Q8l1.Mq0.exv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_exv__2 : gw_eqs.
Lemma gw_eq_eyv__2 : @eyv = ltac:(GwInst.gw_term (@Q8l1.Mq0.eyv) (@eyv)). Proof. unfold eyv, Q8l1.Mq0.eyv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_eyv__2 : gw_eqs.
Lemma gw_eq_sxv__2 : @sxv = ltac:(GwInst.gw_term (@Q8l1.Mq0.sxv) (@sxv)). Proof. unfold sxv, Q8l1.Mq0.sxv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sxv__2 : gw_eqs.
Lemma gw_eq_UX__2 : @UX = ltac:(GwInst.gw_term (@Q8l1.Mq0.UX) (@UX)). Proof. unfold UX, Q8l1.Mq0.UX; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_UX__2 : gw_eqs.
Lemma gw_eq_UY__2 : @UY = ltac:(GwInst.gw_term (@Q8l1.Mq0.UY) (@UY)). Proof. unfold UY, Q8l1.Mq0.UY; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_UY__2 : gw_eqs.
Lemma gw_eq_K_normy__2 : @K_normy = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_normy) (@K_normy)). Proof. unfold K_normy, Q8l1.Mq0.K_normy; rewrite ?gw_eq_sxv__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_K_normy__2 : gw_eqs.
Lemma gw_eq_K_norm__2 : @K_norm = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_norm) (@K_norm)). Proof. unfold K_norm, Q8l1.Mq0.K_norm; rewrite ?gw_eq_exv__2, ?gw_eq_eyv__2, ?gw_eq_UX__2, ?gw_eq_UY__2, ?gw_eq_K_normy__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_K_norm__2 : gw_eqs.
Lemma gw_eq_K_cmp__2 : @K_cmp = ltac:(GwInst.gw_term (@Q8l1.Mq0.K_cmp) (@K_cmp)). Proof. unfold K_cmp, Q8l1.Mq0.K_cmp; rewrite ?gw_eq_UX__2, ?gw_eq_UY__2, ?gw_eq_K_norm__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_K_cmp__2 : gw_eqs.

Lemma rfmodl_spec : rfmodl_stmt.
Proof. rewrite ?gw_eq_rfmodl_stmt; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.rfmodl_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq0.rfmodl_spec)]. Qed.

