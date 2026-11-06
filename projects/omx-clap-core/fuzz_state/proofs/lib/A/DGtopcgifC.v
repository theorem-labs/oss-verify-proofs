(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGtopcgifC.v (a working branch 84ee52cd012, file sha256 82338809aada) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)

(* cgif_file's Deallocate contract at cgif's own model and predicates (the AVIEW post), CLOSED: DGtopcgif's
   adealloc_realizes_cgif_di at L24 = 16385 (the batch bound enq_bridge needs, CLenqcgif.EPc), with its six drain-side
   premises discharged by their instance lemmas:
   - di_drain_cgif (DGif1d.v, a Theorem Labs lane): the released drain walk at the aview frame;
   - di_requar_x_cgif / di_requar_r_cgif / di_requar_e_cgif / di_rchunk_cgif / di_cdealloc_cgif (DGif1dI.v,
     a Theorem Labs lane): the re-quarantine cuts, Recycle and CacheDealloc at the aview frame.
   What is left is the released depot contract tfib_depot_spec and the symbol table TfibSyms, the same two premises
   AGif1.iface_cgif takes on the Allocate side.

   adealloc_realizes_cgif_raw_closed: the RAW-framed twin (DeallocG.adealloc_realizes_raw at cgif), from a Theorem Labs lane's
   DIfaceRcgif.adealloc_realizes_cgif_raw_closed (DGtop's raw corollary over diface_cgif and DIfaceR at cgif, with
   a Theorem Labs lane's CLenqcgifRaw.dr_enqueue_cgif and DGif1.enq_bridge_cgif) fed the same six drain-side lemmas at the
   same L24 = 16385.  Same two premises. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AF0m AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif DGtop DGtopcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGif1d DGif1dI DIfaceRcgif.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem adealloc_realizes_cgif_closed : forall B, TfibSyms B -> tfib_depot_spec B -> adealloc_realizes_cgif B.
Proof.
intros B TS HD1.
exact (adealloc_realizes_cgif_di B TS 16385 HD1 ltac:(lia)
  (DGif1d.di_drain_cgif B TS 16385)
  (DGif1dI.di_requar_x_cgif B TS 16385)
  (DGif1dI.di_requar_r_cgif B TS 16385)
  (DGif1dI.di_requar_e_cgif B)
  (DGif1dI.di_rchunk_cgif B TS)
  (DGif1dI.di_cdealloc_cgif B TS)).
Qed.

Theorem adealloc_realizes_cgif_raw_closed : forall B, TfibSyms B -> tfib_depot_spec B -> adealloc_realizes_cgif_raw B.
Proof.
intros B TS HD1.
exact (DIfaceRcgif.adealloc_realizes_cgif_raw_closed B TS 16385 HD1 ltac:(lia)
  (DGif1d.di_drain_cgif B TS 16385)
  (DGif1dI.di_requar_x_cgif B TS 16385)
  (DGif1dI.di_requar_r_cgif B TS 16385)
  (DGif1dI.di_requar_e_cgif B)
  (DGif1dI.di_rchunk_cgif B TS)
  (DGif1dI.di_cdealloc_cgif B TS)).
Qed.

End a.
