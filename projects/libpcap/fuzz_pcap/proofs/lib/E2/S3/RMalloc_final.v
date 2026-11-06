(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceTB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_malloc_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_calloc_spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free__S3.
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
Section Generic.
Context {PState : Type} {AS : AllocSt PState}.

Theorem rmalloc_spec_u : rmalloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rmalloc_stmt_of_class. intros TB. apply rmalloc_spec. Qed.

Theorem rfree_spec_u : rfree_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rfree_stmt_of_class. intros TB. apply rfree_spec_proof. Qed.

Theorem rcalloc_spec_u : rcalloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rcalloc_stmt_of_class. intros TB. apply rcalloc_spec. Qed.

Theorem rrealloc_spec_u : rrealloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rrealloc_stmt_of_class. intros TB. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc_spec.rrealloc_spec. Qed.

Theorem RHEAP_frame : forall TB : TlsBase, RHEAP_frame_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_frame_proof. Qed.
Theorem RHEAP_init : forall TB : TlsBase, RHEAP_init_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_init_proof. Qed.
Theorem RHEAP_block_range : forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_block_range_proof. Qed.
Theorem RHEAP_blocks_disjoint : forall TB : TlsBase, RHEAP_blocks_disjoint_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_blocks_disjoint_proof. Qed.
Theorem RHEAP_blocks_nodup : forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_blocks_nodup_proof. Qed.

End Generic.

(* [comment removed for export] *)
Theorem hmalloc_spec : hmalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hmalloc_of_rmalloc. apply rmalloc_spec_u. Qed.

Theorem HEAPT_addr : forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> hf_addr h q = A.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_addr_of RHEAP_block_range). Qed.

Theorem HEAPT_range : forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> rblock_rangeu utp A n.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_range_of RHEAP_block_range). Qed.

Theorem HEAPT_disjoint : forall h utp LB m t1 t2, HEAPT h utp LB m -> In t1 LB -> In t2 LB -> tb_tok t1 <> tb_tok t2 ->
  tb_addr t1 + tb_size t1 <= tb_addr t2 \/ tb_addr t2 + tb_size t2 <= tb_addr t1.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_disjoint_of RHEAP_blocks_disjoint RHEAP_blocks_nodup). Qed.

Theorem HEAPT_frame : forall h utp LB m m' W,
  HEAPT h utp LB m -> munch W m m' -> wmono ssegs m m' -> Forall (client_write_okT utp LB) W -> HEAPT h utp LB m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_frame_of RHEAP_frame). Qed.

Theorem HEAPT_init : forall utp m, tls_ok (utp - 200) -> rheap_init_mem m ->
  HEAPT (fheap_init msecret (reservedZ ssegs ++ [(utp - 200, 4096)])) utp [] m.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros utp m H IM. exact (HEAPT_init_of RHEAP_init utp m H IM). Qed.

Theorem hfree_spec : hfree_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hfree_of_rfree; [apply rfree_spec_u | apply RHEAP_blocks_nodup]. Qed.

Theorem hcalloc_spec : hcalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hcalloc_of_rcalloc. apply rcalloc_spec_u. Qed.

Theorem hrealloc_spec : hrealloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hrealloc_of_rrealloc; [apply rrealloc_spec_u | apply RHEAP_blocks_nodup]. Qed.

(* [comment removed for export] *)

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceT.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceTB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_malloc_spec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_calloc_spec.TwB.
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
Section Generic.
Context {PState : Type} {AS : AllocSt PState}.

Theorem rmalloc_spec_u : rmalloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rmalloc_stmt_of_class. intros TB. apply rmalloc_spec. Qed.

Theorem rfree_spec_u : rfree_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rfree_stmt_of_class. intros TB. apply rfree_spec_proof. Qed.

Theorem rcalloc_spec_u : rcalloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rcalloc_stmt_of_class. intros TB. apply rcalloc_spec. Qed.

Theorem rrealloc_spec_u : rrealloc_stmt_u (PState:=PState) (AS:=AS).
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply rrealloc_stmt_of_class. intros TB. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc_spec.TwB.rrealloc_spec. Qed.

Theorem RHEAP_frame : forall TB : TlsBase, RHEAP_frame_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_frame_proof. Qed.
Theorem RHEAP_init : forall TB : TlsBase, RHEAP_init_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_init_proof. Qed.
Theorem RHEAP_block_range : forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_block_range_proof. Qed.
Theorem RHEAP_blocks_disjoint : forall TB : TlsBase, RHEAP_blocks_disjoint_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_blocks_disjoint_proof. Qed.
Theorem RHEAP_blocks_nodup : forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PState) (AS:=AS) (TB:=TB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros TB. apply RHEAP_blocks_nodup_proof. Qed.

End Generic.

(* [comment removed for export] *)
Theorem hmalloc_spec : hmalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hmalloc_of_rmalloc. apply rmalloc_spec_u. Qed.

Theorem HEAPT_addr : forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> hf_addr h q = A.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_addr_of RHEAP_block_range). Qed.

Theorem HEAPT_range : forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> rblock_rangeu utp A n.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_range_of RHEAP_block_range). Qed.

Theorem HEAPT_disjoint : forall h utp LB m t1 t2, HEAPT h utp LB m -> In t1 LB -> In t2 LB -> tb_tok t1 <> tb_tok t2 ->
  tb_addr t1 + tb_size t1 <= tb_addr t2 \/ tb_addr t2 + tb_size t2 <= tb_addr t1.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_disjoint_of RHEAP_blocks_disjoint RHEAP_blocks_nodup). Qed.

Theorem HEAPT_frame : forall h utp LB m m' W,
  HEAPT h utp LB m -> munch W m m' -> wmono usegs m m' -> Forall (client_write_okT utp LB) W -> HEAPT h utp LB m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts. exact (HEAPT_frame_of RHEAP_frame). Qed.

Theorem HEAPT_init : forall utp m, tls_ok (utp - 200) -> rheap_init_mem m ->
  HEAPT (fheap_init msecret (reservedZ usegs ++ [(utp - 200, 4096)])) utp [] m.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros utp m H IM. exact (HEAPT_init_of RHEAP_init utp m H IM). Qed.

Theorem hfree_spec : hfree_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hfree_of_rfree; [apply rfree_spec_u | apply RHEAP_blocks_nodup]. Qed.

Theorem hcalloc_spec : hcalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hcalloc_of_rcalloc. apply rcalloc_spec_u. Qed.

Theorem hrealloc_spec : hrealloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts. apply hrealloc_of_rrealloc; [apply rrealloc_spec_u | apply RHEAP_blocks_nodup]. Qed.

(* [comment removed for export] *)

End WithCeil.
End TwB.
