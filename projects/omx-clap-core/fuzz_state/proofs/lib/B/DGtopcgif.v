(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGtopcgif.v (a working branch ced28ed2383, file sha256 90f0b9cb0591) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; taken by path: no numeral of it names an image address, none changed. *)

(* cgif_file's Deallocate contract at cgif's own model and predicates, from the generic one: DGtop's cgif corollary
   (adealloc_realizes_cgif_of, the AVIEW post) applied to cgif's DIface instance (DGif1.diface_cgif). What is left as
   premises is exactly DGif1's section hypotheses: the depot spec, the batch bound, and the six drain-side fields,
   which are discharged from cgif's released drain walk (DGif1d). *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The cgif image instances first, so that the released tfibsegs lemmas imported below shadow ImgBase's generalised copies. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFew YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif0cgif AGif1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DeallocGcgif DGbase DGgi DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG06 YG07 YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq YFf0 YFfl YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFhd YFhf YFhl YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0o YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB13 YFex YFfy AGix.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require CLdepotcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require CLenqcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGtop DGif1.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem adealloc_realizes_cgif_di : forall B, TfibSyms B -> forall L24, tfib_depot_spec B -> 16385 <= L24 ->
  drain_spec_cf B (ARX_cgif B) (aowned B) drain_body L24 qloose ->
  di_requar_x_t B (ARX_cgif B) (aowned B) L24 qloose ->
  di_requar_r_t B (ARX_cgif B) (ARX_cgif B) (aowned B) L24 qloose (DRq_cgif B) ->
  di_requar_e_t (ARX_cgif B) (ARX_cgif B) (DRq_cgif B) ->
  di_rchunk_t B (ARX_cgif B) (aowned B) (DRq_cgif B) ->
  di_cdealloc_t B (ARX_cgif B) (aowned B) (DRq_cgif B) ->
  adealloc_realizes_cgif B.
Proof.
intros B TS L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd.
exact (adealloc_realizes_cgif_of B TS _ _ _ _ _ _ (diface_cgif B TS L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd)).
Qed.

End a.
