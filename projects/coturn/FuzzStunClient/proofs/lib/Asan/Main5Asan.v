(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: one tree per launch rseq layout: t_53 and t_49 start from the collected templates (TOTmplRAsan, M5TmplRAsan), t_48 is checked from its collected pieces (M5ColA*.v) and the W1 tree is started from HG1_r, in place of the recorded certificates. *)
(* One tree per r. The root t_53 and the node t_49 above the W1 tree (TPH1, a section variable
   started from HG1_r) start from the per-r templates of TOTmplRAsan / M5TmplRAsan (Main5AsanDefs), with
   the plans [psh root_opent] and the per-r [M5TmplRAsan.M5P rsb k], and are assembled from their conjuncts. The
   closed subtree t_48 is the released subtree M5TreeA.M5RelA.t_48 collected by [TreeColA.tcol] from [HO_r rsb], in
   pieces that compile in parallel (M5ColA.v: the root w0r and the chain's leaves; M5ColA3.v / M5ColA3z.v (one per r),
   M5ColA4..6.v: the chain's four
   prefix nodes), put back together here and decided by one [mtree_ok] reflection per r. The subtree is collected
   whole by tcol, not layer-wise by [MainCol.mmj_loop]: t_14 arrives at hole 2100 with a register-only
   difference, which no meet resolves and tcol's respelling handles. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan W0Lib W0States1 W0States2 W0Plans ArgleafTmplAsan ArgleafContOAllAsan VarShift MainCol TOTmplRAsan ContOAll5Asan M5TmplRAsan Main5AsanDefs M5TreeA M5ColA M5ColA3 M5ColA3z M5ColA4 M5ColA5 M5ColA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* ---- the closed subtree t_48: the collected pieces put back in the released chain's order ---- *)
Definition M5P3 (rsb : bool) : mtree := if rsb then M5P3_A1 else M5P3_A0.
Lemma pk3 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) ((((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) (pick 3 (M5P3 rsb)) = true.
Proof. destruct rsb; [exact pk3_1 | exact pk3_0]. Qed.
Definition t_45 (rsb : bool) : mtree :=
  MSplit QFlen 5 (pick 0 (M5L rsb)) (MSplit QRoom (-1) (pick 1 (M5L rsb)) (MSplit QRoom 0 (pick 2 (M5L rsb))
    (MSplit QRoom 5888 (pick 3 (M5P3 rsb)) (MSplit QRoom 7936 (pick 4 (M5P4 rsb)) (MSplit QRoom 64512 (pick 5 (M5P5 rsb))
    (MSplit QRoom 65529 (pick 6 (M5P6 rsb)) (MEmpty 2%nat))))))).
Definition t_48 (rsb : bool) : mtree := MPreX 1%nat (p48 rsb) (HT48 rsb) [(10%nat, t_45 rsb)] (HR48 rsb) (RT48 rsb).
Definition r_47 (rsb : bool) : rtree := RClass m5_CLA (RLeaf (M5P rsb 19)).
Definition r_52 : rtree := RClass C_o_asan (RLeaf cont_o_all_asanR).

(* t_48's check from its pieces' checks (M5ColA*.v: one reflection per piece and r), so no single computation
   carries the whole subtree. *)
Lemma t45_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) C48 (t_45 rsb) = true.
Proof.
  unfold t_45.
  apply mtree_ok_split; [exact (pk0 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk1 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk2 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk3 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk4 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk5 (rsb := rsb)) |].
  apply mtree_ok_split; [exact (pk6 (rsb := rsb)) |].
  apply mtree_ok_empty; vm_compute; reflexivity.
Qed.
Lemma t48_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) C48 (t_48 rsb) = true.
Proof.
  exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) C48 1%nat (p48 rsb) (HT48 rsb) [(10%nat, t_45 rsb)]
           (HR48 rsb) (RT48 rsb) _ eq_refl (c48 (rsb := rsb)) (seg48 (rsb := rsb))
           ltac:(destruct rsb; vm_compute; reflexivity)
           (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat (HT48 rsb) C48 10%nat (t_45 rsb) _ 2%nat (AR0c rsb) (ht48 (rsb := rsb))
              (t45_ok (rsb := rsb)) (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat (HT48 rsb) C48))
           (covs48 (rsb := rsb)) (rf48 (rsb := rsb)) (hf48 (rsb := rsb))).
Qed.

(* ---- t_49 (above TPH1): its conjuncts ---- *)
Definition C49 : class := (root_class 5) ++ [(QFlen, 65535 + 1, QMAX)].
Definition chk49 (rsb : bool) : cres := ta_chk_with rsb C49 (pay_start (HO_r rsb) C49) (hs_ofX (HT_9 rsb) (HR_4 rsb)) (M5P rsb 1).
Definition S49_A1 : shape := Eval vm_compute in match chk49 true with COk s => s | CErr _ _ _ => SNil end.
Definition S49_A0 : shape := Eval vm_compute in match chk49 false with COk s => s | CErr _ _ _ => SNil end.
Definition S49 (rsb : bool) : shape := if rsb then S49_A1 else S49_A0.
Lemma c49 {rsb : bool} : check ASEGS IT_asan (ASAN_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNM rsb (iotab_of C49)) (XEm ASEGS (ASAN_at (rseq_z rsb)) NX0) (XBm ASEGS (ASAN_at (rseq_z rsb)) NX0 (iotab_of C49)) (hs_ofX (HT_9 rsb) (HR_4 rsb)) 0%nat 400000%nat 5000%nat None (pay_start (HO_r rsb) C49) (M5P rsb 1) = COk (S49 rsb).
Proof. destruct rsb; [vm_cast_no_check (eq_refl (COk S49_A1)) | vm_cast_no_check (eq_refl (COk S49_A0))]. Qed.
Lemma seg49 {rsb : bool} : class_seg_ok (lv_of (HT_9 rsb)) 1%nat C49 (subst_holes (rs_ofX (HT_9 rsb) (HR_4 rsb)) (S49 rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma covs49 {rsb : bool} : mcoverS (HR_4 rsb) [(26%nat, r_47 rsb)] = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma rf49 {rsb : bool} : rforest_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan (HR_4 rsb) C49 [(26%nat, r_47 rsb)] = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma hf49 {rsb : bool} : hr_hole_free (HR_4 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.

(* ---- the root t_53: its conjuncts ---- *)
Definition chk53 (rsb : bool) : cres :=
  ta_chk_with rsb (root_class 5) (pay_start (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 5)) (hs_ofX (HT_1 rsb) (HR_2 rsb)) (psh root_opent).
Definition S53_A1 : shape := Eval vm_compute in match chk53 true with COk s => s | CErr _ _ _ => SNil end.
Definition S53_A0 : shape := Eval vm_compute in match chk53 false with COk s => s | CErr _ _ _ => SNil end.
Definition S53 (rsb : bool) : shape := if rsb then S53_A1 else S53_A0.
Lemma c53 {rsb : bool} : check ASEGS IT_asan (ASAN_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNM rsb (iotab_of (root_class 5))) (XEm ASEGS (ASAN_at (rseq_z rsb)) NX0) (XBm ASEGS (ASAN_at (rseq_z rsb)) NX0 (iotab_of (root_class 5))) (hs_ofX (HT_1 rsb) (HR_2 rsb)) 0%nat 400000%nat 5000%nat None (pay_start (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 5)) (psh root_opent) = COk (S53 rsb).
Proof. destruct rsb; [vm_cast_no_check (eq_refl (COk S53_A1)) | vm_cast_no_check (eq_refl (COk S53_A0))]. Qed.
Lemma seg53 {rsb : bool} : class_seg_ok (lv_of (HT_1 rsb)) 0%nat (root_class 5) (subst_holes (rs_ofX (HT_1 rsb) (HR_2 rsb)) (S53 rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma covs53 {rsb : bool} : mcoverS (HR_2 rsb) [(3%nat, r_52)] = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma rf53 {rsb : bool} : rforest_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan (HR_2 rsb) (root_class 5) [(3%nat, r_52)] = true.
Proof.
  exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan (HR_2 rsb) (root_class 5) 3%nat r_52 _ cont_o_all_asan_s (TO_asan_r rsb) eq_refl
           (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan cont_o_all_asan_s (TO_asan_r rsb) (root_class 5) C_o_asan _ eq_refl o_leaf_ok)
           (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan (HR_2 rsb) (root_class 5))).
Qed.
Lemma hf53 {rsb : bool} : hr_hole_free (HR_2 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.

(* ---- the fifth tree: t_49 above the W1 tree TPH1, the split t_50 and the root t_53, per r ---- *)
Section Tree5.
  Context {rsb : bool}.   (* the launch's kb_rseq; the table is ASAN_at/ASAN_at (rseq_z rsb) *)
  Variable TPH1 : mtree.
  Hypothesis TPH1_ok : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat (HG1_r rsb) C49 TPH1 = true.
  Definition t_49 : mtree := MPreX 1%nat (M5P rsb 1) (HT_9 rsb) [(12%nat, TPH1)] (HR_4 rsb) [(26%nat, r_47 rsb)].
  Definition t_50 : mtree := MSplit QFlen 65535 (t_48 rsb) t_49.
  Definition t_53 : mtree := MPreX 0%nat (psh root_opent) (HT_1 rsb) [(1%nat, t_50)] (HR_2 rsb) [(3%nat, r_52)].
  Lemma cov_168 : mcover (HT_9 rsb) [(12%nat, TPH1)] = true.
  Proof. reflexivity. Qed.
  Lemma fo_169 : mforest_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat (HT_9 rsb) C49 [(12%nat, TPH1)] = true.
  Proof.
    exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat (HT_9 rsb) C49 12%nat TPH1 _ 1%nat (HG1_r rsb) eq_refl TPH1_ok
             (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat (HT_9 rsb) C49)).
  Qed.
  Lemma nd_164 : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) C49 t_49 = true.
  Proof.
    exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) C49 1%nat (M5P rsb 1) (HT_9 rsb) [(12%nat, TPH1)]
             (HR_4 rsb) [(26%nat, r_47 rsb)] _ eq_refl (c49 (rsb := rsb)) (seg49 (rsb := rsb)) cov_168 fo_169
             (covs49 (rsb := rsb)) (rf49 (rsb := rsb)) (hf49 (rsb := rsb))).
  Qed.
  Lemma nd_15 : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) (root_class 5) t_50 = true.
  Proof.
    exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat (HO_r rsb) (root_class 5) QFlen 65535 (t_48 rsb) t_49
             (t48_ok (rsb := rsb)) nd_164).
  Qed.
  Lemma cov_14 : mcover (HT_1 rsb) [(1%nat, t_50)] = true.
  Proof. reflexivity. Qed.
  Lemma fo_173 : mforest_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat (HT_1 rsb) (root_class 5) [(1%nat, t_50)] = true.
  Proof.
    exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 0%nat (HT_1 rsb) (root_class 5) 1%nat t_50 _ 1%nat (HO_r rsb) eq_refl nd_15
             (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 0%nat (HT_1 rsb) (root_class 5))).
  Qed.
  Lemma nd_10 : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 5) t_53 = true.
  Proof.
    exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 5) 0%nat
             (psh root_opent) (HT_1 rsb) [(1%nat, t_50)] (HR_2 rsb) [(3%nat, r_52)] _ eq_refl (c53 (rsb := rsb)) (seg53 (rsb := rsb))
             cov_14 fo_173 (covs53 (rsb := rsb)) (rf53 (rsb := rsb)) (hf53 (rsb := rsb))).
  Qed.
  Definition TREE5 : mtree := t_53.
  Lemma TREE5_ok : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 5) TREE5 = true.
  Proof. exact nd_10. Qed.
End Tree5.
