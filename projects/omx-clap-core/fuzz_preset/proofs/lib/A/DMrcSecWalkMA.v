(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecWalkM.v (commit 5ad50e61fc6a, file sha256 9cf1823b5c93) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 3 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: srrm-walk bookkeeping over the already proved walk of __asan::QuarantineCallback::Recycle
   (0x34810)).

   WHAT.  [segGD_M] is DMrcSecWalk.segGD (the secondary recycle walk from 0x34ddc to the munmap ecall, and its
   continuation to the return) on the materialized-page (M) engine.  It splits on own and on map < kLowMemEnd as
   DMrcSecWalk.segGD_f / segGD_t / segGD split, into the four M arms DMrcSecWalkM_flo / _fhi / _tlo / _thi, and gives
   each arm the memset leaf AFfmM.memset_stretch_nwM.  Its post DMrcSecMatA.at_MUN_M is DMrcSecGvA.at_MUN with the
   materialized-page facts (mat_rec / mat_mid at the munmap ecall, mat_rec / mat_gone at the return), relative to mat0,
   the materialized pages at 0x34ddc.  The Section header is DMrcSecWalk.v's (variables, hypotheses FH / GATE, the Let
   cfg0), with the arms' hypothesis QLY (q = ly_Q ly). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFl3 AFeq AFew AFeu AFfm AFk7 DMrcSecGvA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecMatA AFfmM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecWalkM_floA DMrcSecWalkM_fhiA DMrcSecWalkM_tloA DMrcSecWalkM_thiA.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 : Z).
Variables (own small : bool).
Variable mat0 : list word.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34ddc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small.
Hypothesis GATE : forall PB k, 0 < k -> SHAv map <= PB -> PB + k <= SHEv map len ->
madvise_dontneed_ok (m_vmmaps md0) (Z_to_bv 64 PB) (Z_to_bv 64 k) = true.
Hypothesis QLY : q = ly_Q ly.
Local Notation at_MUN_M := (DMrcSecMatA.at_MUN_M W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own mat0).
Local Notation MSM := (AFfmM.memset_stretch_nwM W).
Lemma segGD_f_M : own = false -> small = true -> SRr tfibsegs W cfg0 at_MUN_M.
Proof.
intros OWN SM. destruct (Z_lt_le_dec map kLowMemEnd) as [ZARM|ZARM].
- exact (DMrcSecWalkM_floA.segGD_f_lo_M W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0
    FH GATE QLY MSM OWN SM ZARM).
- exact (DMrcSecWalkM_fhiA.segGD_f_hi_M W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0
    FH GATE QLY MSM OWN SM ZARM).
Qed.
Lemma segGD_t_M : own = true -> small = true -> SRr tfibsegs W cfg0 at_MUN_M.
Proof.
intros OWN SM. destruct (Z_lt_le_dec map kLowMemEnd) as [ZARM|ZARM].
- exact (DMrcSecWalkM_tloA.segGD_t_lo_M W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0
    FH GATE QLY MSM OWN SM ZARM).
- exact (DMrcSecWalkM_thiA.segGD_t_hi_M W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0
    FH GATE QLY MSM OWN SM ZARM).
Qed.
Lemma segGD_M : small = true -> SRr tfibsegs W cfg0 at_MUN_M.
Proof. intros SM. destruct (Bool.bool_dec own true) as [O|O]; [exact (segGD_t_M O SM) | apply Bool.not_true_is_false in O; exact (segGD_f_M O SM)]. Qed.
End WK.
End d.
