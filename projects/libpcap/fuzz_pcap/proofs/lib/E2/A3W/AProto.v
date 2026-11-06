(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Export AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Export ProtoS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation implS segs RNG t Q ms := (@implF node segs (at_nodeA segs) (silA ASHM) (npeekA segs) fstepS _ RNG t Q ms).

(* [comment removed for export] *)
Ltac fstepS_transport HF :=
  lazymatch type of HF with
  | fstepS ?n ?rsp ?RNG ?RNG' =>
      let HA := fresh "HFA" in
      destruct HF as [HA HF]; cbn [fstepS] in HF;
      first [ (* [comment removed for export] *)
              lazymatch eval hnf in (fstepA n rsp RNG RNG') with RNG' = RNG => idtac end;
              let E := fresh in assert (E : RNG' = RNG) by exact HA; subst RNG'; clear HA; try clear HF
            | fstep_transport HA; try match type of HF with True => clear HF end ]
  end.
Tactic Notation "fstepS_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstepS_transport HF.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma implS_ret : forall RNG {R} (r : R) (Q : R -> footprint -> machine_state -> Prop) ms,
  evtF asegs RNG (Q r RNG) ms -> implS asegs RNG (aembed ATOP (SRet r)) (epostF Q) ms.
Proof. intros RNG R r Q ms H. rewrite aembed_ret. apply implF_ret_ok. exact H. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ProtoS.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation implS segs RNG t Q ms := (@implF node segs (at_nodeA segs) (silA ASHM) (npeekA segs) fstepS _ RNG t Q ms).

(* [comment removed for export] *)
Ltac fstepS_transport HF :=
  lazymatch type of HF with
  | fstepS ?n ?rsp ?RNG ?RNG' =>
      let HA := fresh "HFA" in
      destruct HF as [HA HF]; cbn [fstepS] in HF;
      first [ (* [comment removed for export] *)
              lazymatch eval hnf in (fstepA n rsp RNG RNG') with RNG' = RNG => idtac end;
              let E := fresh in assert (E : RNG' = RNG) by exact HA; subst RNG'; clear HA; try clear HF
            | fstep_transport HA; try match type of HF with True => clear HF end ]
  end.
Tactic Notation "fstepS_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstepS_transport HF.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma implS_ret : forall RNG {R} (r : R) (Q : R -> footprint -> machine_state -> Prop) ms,
  evtF asegs RNG (Q r RNG) ms -> implS asegs RNG (aembed ATOP (SRet r)) (epostF Q) ms.
Proof. intros RNG R r Q ms H. rewrite aembed_ret. apply implF_ret_ok. exact H. Qed.
End CANSEC2.
End TwB.
