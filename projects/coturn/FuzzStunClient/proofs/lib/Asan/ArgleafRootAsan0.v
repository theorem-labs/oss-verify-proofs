(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContUAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition HTAsan0 : list (nat * (nat * acs)) := [(0%nat, (0%nat, TU_asan))].
Definition TREEAsan0 : mtree := MPre 0 pfx_u1a HTAsan0 [(0%nat, MClass CC_u_asan CONTUAsan)].
Lemma asan_r0_pfx : pre_check HS_mainA 0%nat 400000%nat 5000%nat IT_asan 0%nat (root_class 0) HTAsan0 pfx_u1a = COk (SHole 0).
Proof. vm_cast_no_check (eq_refl (COk (SHole 0))). Qed.
Lemma asan_r0_seg : class_seg_ok (lv_of HTAsan0) 0 (root_class 0) (SHole 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_r0_cle : class_le (root_class 0) CC_u_asan = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TREEAsan0_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 0) TREEAsan0 = true.
Proof.
  unfold TREEAsan0.
  apply (mtree_ok_pre0 HS_mainA 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (root_class 0) 0%nat pfx_u1a (HTAsan0) [(0%nat, MClass CC_u_asan CONTUAsan)] (SHole 0) eq_refl asan_r0_pfx asan_r0_seg eq_refl).
  apply (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 0%nat (HTAsan0) (root_class 0) 0%nat _ [] 0%nat TU_asan eq_refl); [| apply mforest_ok_nil].
  exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat TU_asan (root_class 0) CC_u_asan CONTUAsan asan_r0_cle CONTUAsan_ok).
Qed.
