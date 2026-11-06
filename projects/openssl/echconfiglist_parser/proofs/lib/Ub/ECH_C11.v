(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_C4_stmt ECH_C4_egs ECH_C11_stmt ECH_C11_find ECH_C11_fail ECH_C11_suitebad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem C11_spec : heap_sr_hyps_x H -> egs_fresh_stmt H -> C11_stmts H.
  Proof.
    intros HX O3. pose proof (proj1 HX) as HH. pose proof (egs_spec H HH O3) as EGS. unfold C11_stmts.
    split; [exact hfind_found_kem|]. split; [exact (hfind_fail_kem H HX EGS)|].
    split; [exact hfind_found_kdf|]. split; [exact (hfind_fail_kdf H HX EGS)|].
    split; [exact hfind_found_aead|]. split; [exact (hfind_fail_aead H HX EGS)|].
    split; [exact suiteok_spec| exact (suitebad_spec H HX EGS)].
  Qed.
End W.
