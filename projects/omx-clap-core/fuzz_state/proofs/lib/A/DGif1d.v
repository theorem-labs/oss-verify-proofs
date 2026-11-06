(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1d.v (a working branch 84ee52cd012, file sha256 d40e526854bd) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: cgif_file's instance of the drain-side fields of DGif0.DIface (DMiface.v types),
   restated from the released drain / DoRecycle walks (YFeu, YFhf, YFhl): the facts DoRecycle reads from AR's ARm are
   exported over ARX_cgif and the recycle invariant DRq_cgif. *)
(* cgif_file's instance of the drain-side fields of the generic Deallocate interface (DGif0.DIface), at the agreed
   instantiation ARX := ARXr := AllocGcgif.ARX_cgif B, AOX := aowned B, DRq := DRq_cgif B (below), QB := qloose,
   dbody := AFeu.drain_body.

   - [dr_drain_cgif] (DIfaceR): the drain over raw memory, DGif1df.tfib_drain_ok_cf with DGif1dr's recycle fields;
   - [di_drain_cgif] (DIface): dr_drain_cgif with its raw conjunct dropped.
   The re-quarantine, Recycle and CacheDealloc instance lemmas (di_requar_*, di_rchunk, di_cdealloc, dr_rchunk,
   dr_cdealloc) live in a Theorem Labs lane's DGif1dI.v; di_rview at cgif is a Theorem Labs lane's rview_cgif (DGif1.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu AFf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhf AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif1dq DGif1da DGif1df.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGif1dr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The cgif recycle invariant: [DRq_cgif B S its zs] with the chunks [its] and the batch objects [zs] still to
   recycle (DGif0.v:253-255). *)
Definition DRq_cgif (B : asyms) (S : astate) (its : list chunk) (zs : list Z) : Prop :=
RIx (as_universe B) 0 0 0 S its [] zs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DIfaceR's drain-side fields (the raw frame): the drain from DGif1df.tfib_drain_ok_cf with the recycle fields of
   DGif1dr.v, and those two recycle fields themselves.                                                              *)
Lemma dr_drain_cgif : forall B, TfibSyms B -> forall L24, drain_spec_raw_cf B (ARX_cgif B) (aowned B) drain_body L24 qloose.
Proof.
intros B TB L24. exact (tfib_drain_ok_cf B TB (DGif1dr.dgif1_rchunk_cgif B TB) (DGif1dr.dgif1_cdealloc_cgif B TB) L24).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DIface's drain-side fields at the aview frame: the raw posts weakened (the raw conjunct dropped).                *)
Lemma di_drain_cgif : forall B, TfibSyms B -> forall L24, drain_spec_cf B (ARX_cgif B) (aowned B) drain_body L24 qloose.
Proof.
intros B TB L24 inst ly X W regs mem md PRE.
eapply amreal_mono; [| exact (dr_drain_cgif B TB L24 inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _).
exists regs', mem', md'. split; [exact Hc | exact HP].
Qed.

End c.
