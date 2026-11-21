(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: one tree per launch rseq layout from the collected template TUTmplRAsan.TU_asan_r, with the prefix plan renumbered by VarShift.psh and each tree decided by one reflection per layout, in place of the recorded certificates. *)
(* One tree per r; HT hole 0 holds [TUTmplRAsan.TU_asan_r rsb]; the prefix plan is renumbered by
   [VarShift.psh]; the whole tree is decided by one [mtree_ok] reflection per r ([TREEAsan1_ok1] r = 1,
   [TREEAsan1_ok0] r = 0), joined in [TREEAsan1_ok]. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan VarShift TUTmplRAsan ArgleafContUAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HTAsan1 (rsb : bool) : list (nat * (nat * acs)) := [(0%nat, (0%nat, TU_asan_r rsb))].
Definition TREEAsan1 (rsb : bool) : mtree := MPre 0 (psh pfx_u3a) (HTAsan1 rsb) [(0%nat, MClass CC_u_asan CONTUAsan)].
Lemma TREEAsan1_ok1 : mtree_ok (rsb := true) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA true (HS_mainA (rseq_z true)) 0%nat) (root_class 1) (TREEAsan1 true) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TREEAsan1_ok0 : mtree_ok (rsb := false) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA false (HS_mainA (rseq_z false)) 0%nat) (root_class 1) (TREEAsan1 false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TREEAsan1_ok {rsb : bool} : mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) (root_class 1) (TREEAsan1 rsb) = true.
Proof. destruct rsb; [exact TREEAsan1_ok1 | exact TREEAsan1_ok0]. Qed.
