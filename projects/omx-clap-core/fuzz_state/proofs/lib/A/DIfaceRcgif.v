(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file. cgif_file's instance of DIfaceR (the raw-frame obligations of the
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DIfaceRcgif.v (a working branch 84ee52cd012, file sha256 8f4471468710) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): fs C5 - diface_r_cgif's U is tr_admit (as_universe B) S tr, the DIface / DIfaceR instance's trace premise, instead of In tr (as_universe B). *)
   generic Deallocate interface, DIfaceR.v), assembled from the proved fields, and its use in DGtop's raw contract. *)
(* The record DIfaceR has four fields, all proved at cgif's instantiation (ARX := ARXr := ARX_cgif B, AOX := aowned B,
   DRq := DRq_cgif B, dpost := CLenqcgifRaw.dpost_enq_cgif B, and dbody / QB as dr_drain_cgif fixes them):
   - dr_enqueue  : CLenqcgifRaw.dr_enqueue_cgif (a Theorem Labs lane; a projection of CLenqcgif.di_enqueue_cgif, whose post
                   CLenq.acall_post_x already carries the raw conjunct). It needs CLenqcgif.enq_bridge B L24, the one
                   walk-side obligation of the Deallocate instance, which nothing proves yet: it is this file's premise;
   - dr_drain    : DGif1d.dr_drain_cgif (a Theorem Labs lane);
   - dr_rchunk   : DGif1dr.dgif1_rchunk_cgif (a Theorem Labs lane; stated at DIfaceR.dr_rchunk_t);
   - dr_cdealloc : DGif1dr.dgif1_cdealloc_cgif (a Theorem Labs lane; stated at DIfaceR.dr_cdealloc_t).
   [diface_r_cgif] is the record; [adealloc_realizes_cgif_raw_of_bridge] is DGtop.adealloc_realizes_cgif_raw_of (:128) at
   it, so cgif's raw-framed Deallocate contract holds given DIface at cgif (a Theorem Labs lane) and the enqueue bridge. The
   record is built with Build_DIfaceR, so no field type is restated here. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGif1d DGif1dr DGtop CLenqcgif CLenqcgifRaw DGif1.
Import ListNotations.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* DIfaceR at cgif. *)
Definition diface_r_cgif B (TB : TfibSyms B) (L24 : Z) (HBR : CLenqcgif.enq_bridge B L24) :=
  Build_DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) (ARX_cgif B) (ARX_cgif B) (aowned B)
    rpre_dealloc_cgif qtight fpre_cgif (CLenqcgifRaw.dpost_enq_cgif B) _ L24 _ (DGif1dr.DRq_cgif B)
    (CLenqcgifRaw.dr_enqueue_cgif B TB L24 HBR) (DGif1d.dr_drain_cgif B TB L24)
    (DGif1dr.dgif1_rchunk_cgif B TB) (DGif1dr.dgif1_cdealloc_cgif B TB).

(* cgif's raw-framed Deallocate contract, from DIface at cgif and the enqueue bridge. *)
Definition adealloc_realizes_cgif_raw_of_bridge B (TB : TfibSyms B) (L24 : Z) (HBR : CLenqcgif.enq_bridge B L24) IF :=
  DGtop.adealloc_realizes_cgif_raw_of B TB (ARX_cgif B) (CLenqcgifRaw.dpost_enq_cgif B) _ L24 _ (DGif1dr.DRq_cgif B) IF
    (diface_r_cgif B TB L24 HBR).

(* With a Theorem Labs lane's DIface instance (DGif1.diface_cgif, c5 072d82e9f63): cgif's raw-framed Deallocate contract
   resting only on diface_cgif's own premises (depot spec, 16385 <= L24, and its six drain-side fields) and the enqueue
   bridge. The binder types are diface_cgif's, inferred, so none of them is restated here. *)
Definition adealloc_realizes_cgif_raw_di B TB L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd (HBR : CLenqcgif.enq_bridge B L24) :=
  adealloc_realizes_cgif_raw_of_bridge B TB L24 HBR (DGif1.diface_cgif B TB L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd).

(* The enqueue bridge is proved in c5 (a Theorem Labs lane's DGif1.enq_bridge_cgif, from 16385 <= L24), so the raw-framed
   Deallocate contract at cgif rests only on diface_cgif's own premises. *)
Definition adealloc_realizes_cgif_raw_closed B TB L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd :=
  adealloc_realizes_cgif_raw_di B TB L24 HD1 HL24 Hdr Hrx Hrr Hre Hrc Hcd (DGif1.enq_bridge_cgif B TB L24 HL24).
End c.

Check diface_r_cgif.
Check adealloc_realizes_cgif_raw_of_bridge.
Print Assumptions adealloc_realizes_cgif_raw_of_bridge.
Check adealloc_realizes_cgif_raw_di.
Print Assumptions adealloc_realizes_cgif_raw_di.
Check adealloc_realizes_cgif_raw_closed.
Print Assumptions adealloc_realizes_cgif_raw_closed.
(* Donor (provenance of this file, origin first): cgif/cgif_file_fuzzer lib/DIfaceRcgif.v (file sha256 8f4471468710; donor not released), ported onto fuzz_state's asan image (pinned sha256 64b53ff86172; addresses read from its unstripped build 7c4afaee248b), module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Then relocated to fuzz_state image A with diface_r_cgif's U = tr_admit (as_universe B) S tr in place of In tr (as_universe B). *)
