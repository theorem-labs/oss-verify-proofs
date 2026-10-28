(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_Chain.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_iface RT_rep D_libiface D_libiface_pem HandoffLIB TopA_iodefs RT_io TopA_io TopA TopA_hs3.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import ClaVerdict Spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_2 : hs_all_ok (inst A_HSm V_F (ELit 2)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_F : fact_ok (kn A_HSm) (KRange (EVar V_F) 2 (2 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_log : s_log (a_ss A_HSm) = [].
Proof. vm_cast_no_check (eq_refl (@nil sentry)). Qed.

(* [comment removed for export] *)
Theorem A_realizes_of : rt_contracts RTA -> forall C : cli_sigA, cli_okA C ->
  image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
Proof.
  intros RC C (HC0 & HT2 & HT3 & LOC0 & LOCP & INITC & FUZZC & CGH).
  exact (topA_realizes C HC0 hs_ok_2 hs_ok_3 HT2 HT3 hs_F hs_log (main_rta RC rta_io C INITC FUZZC LOC0 LOCP CGH)).
Qed.
