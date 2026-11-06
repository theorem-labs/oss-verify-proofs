(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require UnwKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

#[using="Type"] Lemma ucaller_lower : forall d L m (sp s0 ra sp' ra' : word) trC X,
  ucallerA d L m sp s0 ra trC ->
  bv_unsigned sp' <= bv_unsigned sp -> bv_unsigned sp + 16 <= bv_unsigned s0 ->
  ra' = Z_to_bv 64 X -> ACLIENT_LO <= X < ACLIENT_HI ->
  ucallerA d L m sp' s0 ra' trC.
Proof.
  intros d L m sp s0 ra sp' ra' trC X (UC & LEN & S8 & RA & HS0) HSP HS -> HX.
  unfold ucallerA, ACLIENT_LO, ACLIENT_HI in *.
  assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; lia).
  split; [| split; [exact LEN| split; [lia| split; [rewrite EX; lia| right; lia]]]].
  intros PC k HPC HK. specialize (UC PC k HPC HK).
  inversion UC as [prev frame k0 NV | prev frame k0 fp rav LT TOPB AL KP B1 B2 LOW | prev frame k0 fp rav tr LT TOPB AL KP B1 B2 RAV FPV REST]; subst.
  - apply uc_stop. intros (A1 & A2 & A3 & A4). apply NV. repeat split; lia.
  - eapply uc_lowpc; eauto; lia.
  - eapply uc_step; eauto; lia.
Qed.

End CANSEC1.
