(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reserved-interval ledger, the vDSO, the launch input's kernel build): changed HIU_init, ehi_le_reserved_top; added vdso_live_le. *)
(* The initial ubsan heap: the invariant at the start-up state with the initial credit (K0U, B0U). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require HeapIfaceX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk Scfg ShapeAlg SpinAlg Hoare AgentLib MmapSim AllocSim RefNodes HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP MState Mem Cells Step Frame Exec ITree Nodes Decode Image Tac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog KInv KStep MI_Kit MI_Inv MI_Sim MI_Ledger MI_Contracts.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocHINV_u5 MallocBlocks_u5 Malloc_iface_u5 MallocFacts_A_u5 MallocFacts_inv2_u5 F_free_u5 F_free_spec_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import F_syscalls_u5 RMallocRep_u5 RMallocTree_u5 RMalloc_iface_u5 RMalloc_ifaceP_u5 RF_malloc_top_u5 RF_malloc_spec_u5 RF_free_spec_u5 RF_aligned_u5 RF_aligned_spec_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem KLink BrRes.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import Embed_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapInstU.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ehi_le_reserved_top : forall (l : list (word * word)) e, In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e He; [destruct He|].
  cbn [reserved_top]. destruct He as [<-|He].
  - unfold ehi. cbn [fst snd]. lia.
  - specialize (IH e He). lia.
Qed.

(* LPS 727298f3: the vDSO pair [State.init_reserved] appends to the launch ledger spans at most 20 pages
   ([State.vdso_text_pages_le]). *)
Lemma vdso_live_le : forall kb top, live_bytes (vdso_reserved kb top) <= 20 * 4096.
Proof.
  intros kb top. pose proof (vdso_text_pages_pos kb) as P1. pose proof (vdso_text_pages_le kb) as P2.
  unfold vdso_reserved. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - cbn [live_bytes]. lia.
  - cbn [live_bytes snd]. rewrite !u64_lit; unfold vdso_vvar_pages, page_size; lia.
Qed.

Section INITU.
Variable sptop : Z.

Theorem HIU_init : forall (M : word -> option byte) (lim : Z) (VM : VmMaps),
  lim <= XLIM -> init_statics0 sptop M -> init_vm (L0U sptop) lim VM ->
  hi_heap (HIU sptop) [] (hl_K0 (L0U sptop), hl_B0 (L0U sptop)) M VM.
Proof.
  intros M lim VM HLIM H HVM.
  (* LPS 727298f3: the launch ledger is [State.init_reserved] (the image's reservations and the vDSO
     pair); [HI0_init] builds the invariant over it at the credit (K0, B0), lowered here to (K0U, B0U) *)
  assert (HVM0 : init_vm (L0 sptop) lim VM).
  { destruct HVM as (brk0 & mbase & isp & kb & E & R). exists brk0, mbase, isp, kb. exact (conj E R). }
  pose proof (HI0_init sptop M lim VM HLIM H HVM0) as H0.
  change (hi_heap0 sptop [] (K0, B0) M VM) in H0.
  change (hi_heap0 sptop [] (K0U, B0U) M VM /\ GU (K0U, B0U) VM).
  pose proof K0_val as HK0.
  split; [apply (hi_heap0_cr_le sptop [] K0 B0 K0U B0U M VM H0); unfold K0U, B0U; lia|].
  destruct H0 as (R0 & s & L & LBb & nc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN & _).
  destruct HVM as (brk0 & mbase & isp & kb & -> & _).
  unfold GU. cbn [vm_maps vm_reserved fst snd live_bytes] in LEN |- *. rewrite app_nil_r in LEN |- *.
  unfold init_reserved in LEN |- *. rewrite live_bytes_app.
  change (segments_reserved (hl_segs (L0U sptop))) with RESV in LEN |- *.
  rewrite RESV_live.
  match goal with |- context [live_bytes (vdso_reserved kb ?t)] => pose proof (vdso_live_le kb t) as HV end.
  unfold B0U, CAPG, RESVMAX. splits; lia.
Qed.

End INITU.
