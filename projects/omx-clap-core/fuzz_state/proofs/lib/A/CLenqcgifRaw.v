(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/CLenqcgifRaw.v (a working branch 84ee52cd012, file sha256 efb4361fbbdc) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): fs C5 - U is tr_admit (as_universe B) S tr, the DIface / DIfaceR instance's trace premise, instead of In tr (as_universe B); the proof does not change. *)
(* Modified by Theorem Labs, 2026-10: new file.  cgif_file's [dr_enqueue] field of DIfaceR (DIfaceR.v): QuarantineCache::
   Enqueue at Put's call with the raw frame, [enq_spec_g (acall_raw_x B (aowned B))] at cgif's instance (U := tr_admit
   (as_universe B) S tr, ARX := ARX_cgif, AOX := aowned, rpre := rpre_dealloc_cgif, lpost := qtight, fpre := fpre_cgif,
   dpost := CLdepot.dpost_x, QB := qloose), for a Theorem Labs lane's DIfaceRcgif.diface_r_cgif_of_enq. *)

(* No new walk: CLenqcgif.di_enqueue_cgif already proves the enqueue with CLenq.acall_post_x, whose seventh conjunct
   IS the raw frame (CLenq.v: `forall x : word, ~ AOX ly S .. -> ~ AOX ly' S' .. -> ~ ascratch B stk regs .. -> ~ E .. ->
   mem' x = mem x`, from the arms' walk frames YFgp.MEQ and their twins).  DIfaceR's post splits that into
   DMspec.acall_post_x (the other seven conjuncts) and acall_raw_x (the raw one); this file is that split.
   Like DGif0.di_enqueue at cgif, it takes CLenqcgif.enq_bridge (the enq_pre_x at the quarantined state, owned by the
   Deallocate instance's walk geometry) as its premise.
   rule 24: proves function Allocator::QuarantineChunk / Recycle enqueue path raw frame (kind: callee-contract field,
   PORTED from CLenqcgif.di_enqueue_cgif; reuse search: proof-index QuarantineCache::Enqueue 0 named / 0 by
   address / 0 unreleased; no ref has dr_enqueue_cgif). *)
(* Donor (provenance of this file, origin first): cgif/cgif_file_fuzzer lib/CLenqcgifRaw.v (file sha256 efb4361fbbdc; donor not released), ported onto fuzz_state's asan image (pinned sha256 64b53ff86172; addresses read from its unstripped build 7c4afaee248b), module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Then relocated to fuzz_state image A with U = tr_admit (as_universe B) S tr in place of In tr (as_universe B); the proof does not change. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLdepot CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require CLenqcgif.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* cgif's Deallocate depot answer (DIfaceRcgif's dpost_cgif). *)
Definition dpost_enq_cgif (B : asyms) : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop :=
  fun inst ly S W tr z => CLdepot.dpost_x tfibsegs B inst ly S W tr z.

Theorem dr_enqueue_cgif : forall B, TfibSyms B -> forall L24, CLenqcgif.enq_bridge B L24 ->
  enq_spec_g B (fun tr S => tr_admit (as_universe B) S tr) (ARX_cgif B) (aowned B) rpre_dealloc_cgif qtight fpre_cgif
    (dpost_enq_cgif B) L24 qloose (acall_raw_x B (aowned B)).
Proof.
intros B TB L24 BR inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14
  H15 H16 H17 H18 H19 H20 H21 H22 H23.
eapply amreal_mono;
[| exact (CLenqcgif.di_enqueue_cgif B TB L24 BR (CLenqcgif.refill_specR_cgif B TB)
     inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
     H18 H19 H20 H21 H22 H23)].
cbv beta. intros r W' c' (regs' & mem' & md' & nb & Hc & HP & R).
destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
exists regs', mem', md', nb. split; [exact Hc|].
split; [exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P8))))))|].
split; [exact P7|].
exact R.
Qed.
End a.
