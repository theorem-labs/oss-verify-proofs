(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_state RT_rep RT_facts TopA_iodefs RT_io RT_cli Pj_defsA Pj_os_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_os_ro : forall Σ m, ART_A Σ m -> pj_os_roA m.
Proof.
  intros Σ m HA. pose proof (rta_cli_ro Σ m HA) as C. unfold pj_os_roA.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_GOT_VT_A, PJ_SB_BVT_A, PJ_IOS_BVT_A, PJ_WIDEN_SLOT_A, PJ_DO_WIDEN_A,
         PJ_GOT_CTYPE_ID_A, PJ_CTYPE_ID_A.
  split; [| split; [| split]]; (apply (cli_ro_at m); [exact C | cli_in]).
Qed.
