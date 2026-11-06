(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Rep
     ECH_C4_stmt ECH_C3_stmt ECH_C14_stmt ECH_Iface ECH_C14_readcfg ECH_C14_entry ECH_C14_b64arm ECH_Certs F_time MallocSR MallocSR_closed.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import CertA_plain CertO3_plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section G.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem readcfg_closed : heap_sr_hyps_x H -> time_sr_stmt H -> readcfg_stmt H.
  Proof.
    intros HX TIME. eapply (readcfg_spec H HX (egs_fresh_cert H HX) TIME).
    - intros. eapply (rp_entry H HX (egs_fresh_cert H HX)); eassumption.
    - intros. eapply (rp_b64arm H HX (egs_fresh_cert H HX) (getdefctx_fresh_cert H HX)); try eassumption.
      intros. eapply (rp_entry H HX (egs_fresh_cert H HX)); eassumption.
  Qed.

  Theorem fuzz_closed_x : heap_sr_hyps_x H -> time_sr_stmt H -> fuzz_stmt H.
  Proof. intros HX TIME. exact (fuzz_spec_x H HX (readcfg_closed HX TIME)). Qed.
End G.

Theorem fuzz_closed : forall (HCEIL : HeapCeil) (HSEC : HeapSecret), @ECH_Iface.fuzz_stmt HCEIL (@MallocSR.HS HCEIL HSEC).
Proof. intros HCEIL HSEC. apply fuzz_closed_x; [apply heap_sr_hyps_x_closed| apply time_sr]. Qed.

Print Assumptions fuzz_closed.
