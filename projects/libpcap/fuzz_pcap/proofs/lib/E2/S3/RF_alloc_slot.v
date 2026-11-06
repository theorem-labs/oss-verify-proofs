(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require ASlot_M0. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.ASlot_M0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_P__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_meta. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RASlot_M1__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RASlot_M1__S3.RASlot_M6.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv4.ist_ampre_proof fuel).
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.ASlot_M0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RASlot_M1__S3.RASlot_M6.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv4.ist_ampre_proof fuel).
Qed.

End PORT.

End WithCeil.
End TwB.
