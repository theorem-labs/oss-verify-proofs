(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition CC_u_asan : class := [(QLook, 0, 0)].
(* [comment removed for export] *)
Definition asan_cu_0_C : class := (CC_u_asan ++ [(QL0, QMIN, 0)]).
Definition asan_cu_0_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SExit 2).
Lemma asan_cu_0 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_0_C cont_u0a = COk asan_cu_0_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_0_s)). Qed.
Lemma asan_cu_0_shape : class_pay_ok 0 asan_cu_0_C asan_cu_0_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_cu_1_C : class := (CC_u_asan ++ [(QL0, 1, QMAX); (QL0, QMIN, 63)]).
Definition asan_cu_1_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SExit 2).
Lemma asan_cu_1 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_1_C cont_u5a = COk asan_cu_1_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_1_s)). Qed.
Lemma asan_cu_1_shape : class_pay_ok 0 asan_cu_1_C asan_cu_1_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_cu_64_C : class := (CC_u_asan ++ [(QL0, 1, QMAX); (QL0, 64, QMAX); (QL0, QMIN, 64)]).
Definition asan_cu_64_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SExit 2).
Lemma asan_cu_64 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_64_C cont_u64a = COk asan_cu_64_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_64_s)). Qed.
Lemma asan_cu_64_shape : class_pay_ok 0 asan_cu_64_C asan_cu_64_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_cu_65_C : class := (CC_u_asan ++ [(QL0, 1, QMAX); (QL0, 64, QMAX); (QL0, 65, QMAX); (QL0, QMIN, 66)]).
Definition asan_cu_65_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SExit 2).
Lemma asan_cu_65 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_65_C cont_u65a = COk asan_cu_65_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_65_s)). Qed.
Lemma asan_cu_65_shape : class_pay_ok 0 asan_cu_65_C asan_cu_65_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_cu_67_C : class := (CC_u_asan ++ [(QL0, 1, QMAX); (QL0, 64, QMAX); (QL0, 65, QMAX); (QL0, 67, QMAX); (QL0, QMIN, 73)]).
Definition asan_cu_67_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SExit 2)).
Lemma asan_cu_67 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_67_C cont_u70a = COk asan_cu_67_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_67_s)). Qed.
Lemma asan_cu_67_shape : class_pay_ok 0 asan_cu_67_C asan_cu_67_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_cu_74_C : class := (CC_u_asan ++ [(QL0, 1, QMAX); (QL0, 64, QMAX); (QL0, 65, QMAX); (QL0, 67, QMAX); (QL0, 74, QMAX)]).
Definition asan_cu_74_s : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SExit 2)).
Lemma asan_cu_74 : pay_check 0%nat 400000%nat 5000%nat IT_asan TU_asan asan_cu_74_C cont_u100a = COk asan_cu_74_s.
Proof. vm_cast_no_check (eq_refl (COk asan_cu_74_s)). Qed.
Lemma asan_cu_74_shape : class_pay_ok 0 asan_cu_74_C asan_cu_74_s = true.
Proof. vm_compute. reflexivity. Qed.

Definition CONTUAsan : mtree := MSplit QL0 0 (MLeaf 0 cont_u0a) (MSplit QL0 63 (MLeaf 0 cont_u5a) (MSplit QL0 64 (MLeaf 0 cont_u64a) (MSplit QL0 66 (MLeaf 0 cont_u65a) (MSplit QL0 73 (MLeaf 0 cont_u70a) (MLeaf 0 cont_u100a))))).
Lemma CONTUAsan_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan CC_u_asan CONTUAsan = true.
Proof.
  unfold CONTUAsan.
  apply mtree_ok_split; [exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_0 asan_cu_0_shape) |].
  apply mtree_ok_split; [exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_1 asan_cu_1_shape) |].
  apply mtree_ok_split; [exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_64 asan_cu_64_shape) |].
  apply mtree_ok_split; [exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_65 asan_cu_65_shape) |].
  apply mtree_ok_split; [exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_67 asan_cu_67_shape) |].
  exact (mtree_ok_leafP 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan _ 0%nat _ _ eq_refl asan_cu_74 asan_cu_74_shape).
Qed.
