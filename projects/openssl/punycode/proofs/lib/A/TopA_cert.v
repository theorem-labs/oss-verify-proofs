(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import A_Chain.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import RT_iface RT_rep D_libiface Fz_defs TopA_iodefs RT_io TopA_io TopA.
From OSSVerify.Proofs.openssl.punycode.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_2 : hs_all_ok (inst A_HSm V_F (ELit 2)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3 : hs_all_ok (inst A_HSm V_F (ELit 3)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_F : fact_ok (kn A_HSm) (KRange (EVar V_F) 2 (2 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_log : s_log (a_ss A_HSm) = [].
Proof. vm_cast_no_check (eq_refl (@nil sentry)). Qed.

(* [comment removed for export] *)
Theorem A_realizes_of : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
Proof.
  intros RC FUZZ. exact (topA_realizes hs_ok_2 hs_ok_3 hs_F hs_log (main_rta RC rta_io FUZZ)).
Qed.
