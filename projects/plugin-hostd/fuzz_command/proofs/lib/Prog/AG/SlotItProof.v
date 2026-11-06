(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v, with its module paths and numbers changed; 526 of its 771 lines of code are new or changed and 145 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/AG/SlotItB3h.v, with its module paths and module names changed; 31 of its 57 lines of code are new or changed and 745 lines of the source are left out. *)
(* lib/Prog/SlotItProof.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotCallees SlotIter SlotItBase SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItA SlotItB SlotItBW SlotItC0 SlotItCW SlotItD.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c check_arity_c memcpy_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotInv.
Import ListNotations.
Local Open Scope Z_scope.

Section ItProof.

Hypothesis HB2 : forall (rc : RunCeil) (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound),
  Slot.frame_given B API LS SH SK ra empty ->
  lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b ->
  spZ rg = S ->
  check_reply_contract -> check_arity_contract -> memcpy_contract -> strspn_contract -> strcspn_contract ->
  forall (m p n : Z) (R0 : rstate) (c : config),
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> 0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
  stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).

Lemma iter_spec_holds : SlotIter.iter_spec.
Proof.
  intros B API LS SH SK ra empty rc S rg mem0 md0 L0 A0 p0 n0 pl b FG CC HPR PRE RG2 m c HH.
  destruct CC as (SMC & CWC & CRTC & RCC & CRPC & CARC & CRFC & SNLC & MCC & SSPC & SCSC).
  specialize (SMC rc). specialize (CWC rc). specialize (CRTC rc).
  eapply SR_bind; [eapply SlotItA.ia_head; eassumption|].
  intros c1 (p & n & R0 & HA).
  assert (DCL : r_refuse R0 <> 0 -> declared (r_code R0) = true).
  { destruct HA as (fx & L & A & regs & mem & md & O & q & _ & _ & _ & _ & _ & H & _). exact H. }
  assert (RNG : 0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64).
  { destruct HA as (fx & L & A & regs & mem & md & O & q & _ & _ & _ & (REP & _) & _).
    destruct (it_rep_parts L A mem R0 O REP) as [_ (_ & _ & _ & _ & _ & X6)]. lia. }
  destruct RNG as [RS RH].
  eapply SR_bind; [eapply SlotItA.ia_send; eassumption|].
  intros c2 HSA.
  eapply SR_bind; [eapply SlotItB.ib_seg; eassumption|].
  intros c3 HSB.
  eapply SR_bind;
    [exact (HB2 rc B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 CRPC CARC MCC SSPC SCSC
              m p n R0 c3 DCL RS RH HSB)|].
  intros c4 HBW.
  eapply SR_bind; [eapply SlotItCW.seg_c; eassumption|].
  intros c5 HC.
  eapply SlotItD.seg_de; eassumption.
Qed.

End ItProof.
