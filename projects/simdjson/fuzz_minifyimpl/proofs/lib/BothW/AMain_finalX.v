(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import BothMainU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Stdio AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg ALayout AMalloc_iface AIos_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_closed AMain_closedI AFreeAll
     AMain_final AIcptU_defs AIcptU_ferr AIcptU_fout AIcptU_fw AIcptU_wdefs AIcptU_wcr AExitU_xp.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Set Keyed Unification.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem both_impl_closed : asan_client_stmt -> impl_stmt ASTAGE.
Proof.
  intros CLIENT.
  exact (both_impl_final (fun rc : runConstT => @XPi rc)
           (fun rc : runConstT =>
              @xp_closed rc (fun T => @wcrtomb0_proof rc T) (fun T => @fwrite0_out_proof rc T) (fun T => @fwrite0_err_proof rc T)
                (fun T St get_so set_so GS SS SG => @fflush_out_proof rc T St get_so set_so GS SS SG) (fun T => @fflush_err_proof rc T)
                (AI_of (@AHI_free rc)) (aheap_init (AI_of (@AHI_free rc)) (AI_of_E (@AHI_free rc)))) CLIENT).
Qed.
