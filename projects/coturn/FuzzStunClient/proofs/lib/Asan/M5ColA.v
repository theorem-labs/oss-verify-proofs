(* SPDX-License-Identifier: MIT *)
(* Main5Asan's t_48 subtree, collected per r by [TreeColA.tcol] from [TOTmplRAsan.HO_r rsb] (rsb = true: r = 1; rsb = false:
   r = 0), in pieces so that the pieces compile in parallel: this file collects the root node w0r (its tables for
   holes 10 and 26 and the leaf below hole 26) and the three leaves t_1, t_2, t_3 of the MSplit chain below hole 10;
   M5ColA3..6.v collect the chain's prefix nodes t_14, t_25, t_32, t_37 from the root's collected hole-10 entry.
   Main5Asan.v puts the pieces back together and checks the whole subtree. Nothing here is trusted. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan W0Plans VarShift MainCol TOTmplRAsan TreeColA M5TreeA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition C48 : class := (root_class 5) ++ [(QFlen, QMIN, 65535)].
Definition M5Root : mtree := MPreX 1%nat w0r M5RelA.HT_3 [(10%nat, MEmpty 2%nat)] M5RelA.HR_4 [(26%nat, M5RelA.r_47)].
Definition M5R_A1 : mtree := Eval vm_compute in fst (tcol true esh (HO_r true) C48 M5Root).
Definition M5R_A0 : mtree := Eval vm_compute in fst (tcol false esh (HO_r false) C48 M5Root).
Definition M5R (rsb : bool) : mtree := if rsb then M5R_A1 else M5R_A0.
(* the root's collected hole-10 entry: the start of every node of the chain *)
Definition AR0c (rsb : bool) : acs :=
  match M5R rsb with MPreX _ _ HT _ _ _ => match lkT HT 10 with Some s => s | None => HO_r rsb end | _ => HO_r rsb end.
Definition M5L_A1 : mtree := Eval vm_compute in fst (tcol true esh (AR0c true) C48 (mkeep (fun d => Nat.leb d 2) 0 M5RelA.t_45)).
Definition M5L_A0 : mtree := Eval vm_compute in fst (tcol false esh (AR0c false) C48 (mkeep (fun d => Nat.leb d 2) 0 M5RelA.t_45)).
Definition M5L (rsb : bool) : mtree := if rsb then M5L_A1 else M5L_A0.

(* ---- the subtree's check, in pieces: the root node's conjuncts here, each chain node's in its own file ---- *)
Definition p48 (rsb : bool) : plan := match M5R rsb with MPreX _ p _ _ _ _ => p | _ => PExit end.
Definition HT48 (rsb : bool) : list (nat * (nat * acs)) := match M5R rsb with MPreX _ _ HT _ _ _ => HT | _ => [] end.
Definition HR48 (rsb : bool) : list (nat * (shape * acs)) := match M5R rsb with MPreX _ _ _ _ HR _ => HR | _ => [] end.
Definition RT48 (rsb : bool) : list (nat * rtree) := match M5R rsb with MPreX _ _ _ _ _ RT => RT | _ => [] end.
Definition chk48 (rsb : bool) : cres := ta_chk_with rsb C48 (pay_start (HO_r rsb) C48) (hs_ofX (HT48 rsb) (HR48 rsb)) (p48 rsb).
Definition S48_A1 : shape := Eval vm_compute in match chk48 true with COk s => s | CErr _ _ _ => SNil end.
Definition S48_A0 : shape := Eval vm_compute in match chk48 false with COk s => s | CErr _ _ _ => SNil end.
Definition S48 (rsb : bool) : shape := if rsb then S48_A1 else S48_A0.
Lemma c48 {rsb : bool} : check ASEGS IT_asan (ASAN_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNM rsb (iotab_of C48)) (XEm ASEGS (ASAN_at (rseq_z rsb)) NX0) (XBm ASEGS (ASAN_at (rseq_z rsb)) NX0 (iotab_of C48)) (hs_ofX (HT48 rsb) (HR48 rsb)) 0%nat 400000%nat 5000%nat None (pay_start (HO_r rsb) C48) (p48 rsb) = COk (S48 rsb).
Proof. destruct rsb; [vm_cast_no_check (eq_refl (COk S48_A1)) | vm_cast_no_check (eq_refl (COk S48_A0))]. Qed.
Lemma seg48 {rsb : bool} : class_seg_ok (lv_of (HT48 rsb)) 1%nat C48 (subst_holes (rs_ofX (HT48 rsb) (HR48 rsb)) (S48 rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma ht48 {rsb : bool} : ht_of (HT48 rsb) 10 = Some (2%nat, AR0c rsb).
Proof. destruct rsb; vm_compute; reflexivity. Qed.
Lemma covs48 {rsb : bool} : mcoverS (HR48 rsb) (RT48 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma rf48 {rsb : bool} : rforest_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan (HR48 rsb) C48 (RT48 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma hf48 {rsb : bool} : hr_hole_free (HR48 rsb) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma pk0 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) (C48 ++ [(QFlen, QMIN, 5)]) (pick 0 (M5L rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma pk1 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) ((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) (pick 1 (M5L rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
Lemma pk2 {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat (AR0c rsb) (((C48 ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) (pick 2 (M5L rsb)) = true.
Proof. destruct rsb; vm_cast_no_check (eq_refl true). Qed.
