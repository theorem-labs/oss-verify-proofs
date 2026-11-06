(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_C4_stmt
     ECH_C4_egs ECH_C4_seterr ECH_C4_new ECH_C4_debug ECH_C4_clear.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem C4_spec : heap_sr_hyps_x H -> egs_fresh_stmt H -> C4_stmts H.
  Proof.
    intros HX O3. pose proof (proj1 HX) as HH. pose proof (egs_spec H HH O3) as EGS. unfold C4_stmts.
    split; [exact egs_ready_spec|]. split; [exact EGS|]. split; [exact (errnew_spec H HX EGS)|].
    split; [exact (errdebug_spec H HX)|]. split; [exact errseterr_spec| exact (errclear_spec H HX EGS)].
  Qed.
End W.
