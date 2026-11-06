(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.openssl.pem.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import B_Chain.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import RT_iface RT_rep D_libiface D_libiface_pem HandoffLIB TopA_iodefs RT_io TopA_io TopA TopA_hs3.
From OSSVerify.Proofs.openssl.pem.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_2 : hs_all_ok (inst B_HSm V_F (ELit 2)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_F : fact_ok (kn B_HSm) (KRange (EVar V_F) 2 (2 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_log : s_log (a_ss B_HSm) = [].
Proof. vm_cast_no_check (eq_refl (@nil sentry)). Qed.

(* [comment removed for export] *)
Theorem A_realizes_of : rt_contracts RTA -> forall C : cli_sigA, cli_okA C ->
  image_realizes AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs target_alloc_limit Spec.spec.
Proof.
  intros RC C (HC0 & HT2 & HT3 & LOC0 & LOCP & INITC & FUZZC & CGH).
  exact (topA_realizes C HC0 hs_ok_2 hs_ok_3 HT2 HT3 hs_F hs_log (main_rta RC rta_io C INITC FUZZC LOC0 LOCP CGH)).
Qed.
