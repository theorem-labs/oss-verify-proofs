(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface
     ECH_C3_stmt ECH_C4_stmt ECH_C11_stmt ECH_C7_stmt ECH_C14_stmt ECH_C15_stmt ECH_Iface ECH_C3 ECH_C4 ECH_C11 ECH_C7 ECH_C15_parse ECH_C15_top.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import CertA_plain CertO3_plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem C3_spec_x : heap_sr_hyps_x H -> C3_stmts H.
  Proof. intros HX. exact (C3_spec H HX (getdefctx_fresh_cert H HX)). Qed.

  Theorem C4_spec_x : heap_sr_hyps_x H -> C4_stmts H.
  Proof. intros HX. exact (C4_spec H HX (egs_fresh_cert H HX)). Qed.

  Theorem C11_spec_x : heap_sr_hyps_x H -> C11_stmts H.
  Proof. intros HX. exact (C11_spec H HX (egs_fresh_cert H HX)). Qed.

  Theorem C7_spec_x : heap_sr_hyps_x H -> C7_stmts H.
  Proof. intros HX. exact (C7_spec H HX (getdefctx_fresh_cert H HX)). Qed.

  Theorem parse_one_spec_x : heap_sr_hyps_x H -> readcfg_stmt H -> parse_one_stmt H.
  Proof. intros HX RC. exact (parse_one_spec H HX (getdefctx_fresh_cert H HX) RC). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_spec_x : heap_sr_hyps_x H -> readcfg_stmt H -> fuzz_stmt H.
  Proof. intros HX RC. exact (fuzz_spec H HX (getdefctx_fresh_cert H HX) (egs_fresh_cert H HX) RC). Qed.
End W.

Print Assumptions C3_spec_x.
Print Assumptions C4_spec_x.
Print Assumptions C11_spec_x.
Print Assumptions fuzz_spec_x.
