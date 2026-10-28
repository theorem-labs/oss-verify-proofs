(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The initial ubsan heap: the invariant at the start-up state with the initial credit (K0U, B0U). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require HeapIfaceX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk Scfg ShapeAlg SpinAlg Hoare AgentLib MmapSim AllocSim RefNodes HeapIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP MState Mem Cells Step Frame Exec ITree Nodes Decode Image Tac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog KInv KStep MI_Kit MI_Inv MI_Sim MI_Ledger MI_Contracts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocHINV_u5 MallocBlocks_u5 Malloc_iface_u5 MallocFacts_A_u5 MallocFacts_inv2_u5 F_free_u5 F_free_spec_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import F_syscalls_u5 RMallocRep_u5 RMallocTree_u5 RMalloc_iface_u5 RMalloc_ifaceP_u5 RF_malloc_top_u5 RF_malloc_spec_u5 RF_free_spec_u5 RF_aligned_u5 RF_aligned_spec_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem KLink BrRes.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import Embed_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapInstU.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* Every reserved entry ends at or below the top of the reservations. *)
Lemma ehi_le_reserved_top : forall (l : list (word * word)) e, In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e He; [destruct He|].
  cbn [reserved_top]. destruct He as [<-|He].
  - unfold ehi. cbn [fst snd]. lia.
  - specialize (IH e He). lia.
Qed.

Section INITU.
Variable sptop : Z.

Theorem HIU_init : forall (M : word -> option byte) (lim : Z) (VM : VmMaps),
  lim <= XLIM -> init_statics0 sptop M -> init_vm (L0U sptop) lim VM ->
  hi_heap (HIU sptop) [] (hl_K0 (L0U sptop), hl_B0 (L0U sptop)) M VM.
Proof.
  intros M lim VM HLIM H HVM.
  destruct H as (NONE & NL & PS & GOT & (canary & Hcan & GUARD)
    & (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & secret & AUXC & AVL & RND
       & Bav & Hav & Brnd & Hrnd & X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & Xr & Xs) & MI).
  destruct HVM as (brk0 & mbase & isp & HVMe & VB & _ & VSP & Hisp). subst VM.
  change (bv_unsigned isp = sptop) in Hisp.
  change (valid_brk rsegs brk0) in VB.
  destruct VB as (VB1 & VB2 & VB3).
  change (segments_reserved rsegs) with RESV in VB1, VB2.
  rewrite reserved_top_RESV in VB1, VB2.
  unfold brk_aslr_max, page_size in *.
  destruct VSP as (SP1 & SP2 & _). unfold sp_window_lo, sp_window_hi in *.
  assert (HIMG : 0 < IMG_HI < 2 ^ 32) by (split; apply Z.ltb_lt; vm_compute; reflexivity).
  assert (Hrange : CEIL_LO <= sptop - 2 ^ 23 <= CEIL_HI) by (unfold CEIL_LO, CEIL_HI; lia).
  pose (R0 := mkRunP (sptop - 2 ^ 23) Hrange secret Xs canary Hcan).
  assert (HCEIL : @alloc_ceiling R0 = sptop - 2 ^ 23) by reflexivity.
  destruct (@RHEAP_init_proof R0 M (Z_to_bv 64 av) NONE NL AUXC PS GOT GUARD MI) as [HR HAUX].
  pose proof K0_val as HK0. pose proof NSEG_val as HNSEG.
  assert (HRL : Z.of_nat (length RESV) = 4) by (rewrite RESV_eq; reflexivity).
  change (hi_heap0 sptop [] (K0U, B0U) M (mkVmMapsFull RESV [] [] brk0 brk0 lim mbase isp)
          /\ GU (K0U, B0U) (mkVmMapsFull RESV [] [] brk0 brk0 lim mbase isp)).
  split.
  2:{ unfold GU. cbn [vm_maps vm_reserved fst snd live_bytes]. rewrite app_nil_r, HRL.
      unfold B0U, CAPG, K0U. lia. }
  exists R0, (@ps_init R0 (reservedZ rsegs)), (led_init (reservedZ rsegs)), [], 0.
  cbn [fst snd vm_reserved vm_maps vm_limit].
  rewrite app_nil_r.
  splits.
  - exact HCEIL.
  - reflexivity.
  - exact HR.
  - unfold ps_init. cbn [ps_m]. apply creach_init.
  - apply Permutation_refl.
  - constructor; cbn [vm_maps vm_noaccess vm_reserved vm_start_brk vm_brk vm_init_sp
                      ld_resv ld_groups ld_metas ld_brkreg ld_brk led_init].
    + split; [intros e []|constructor].
    + intros e [].
    + reflexivity.
    + reflexivity.
    + intros e He. pose proof (ehi_le_reserved_top RESV e He) as Hle.
      rewrite reserved_top_RESV in Hle. lia.
    + rewrite HCEIL. unfold PGSZ. lia.
    + intros b l [].
    + intros b l k [].
    + constructor.
    + intros b l Hb. discriminate.
    + split; reflexivity.
    + rewrite HCEIL. lia.
  - exact MI.
  - exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd.
    refine (conj HAUX (conj AVL (conj RND _))). rewrite HCEIL. lia.
  - intros a Ha. apply NONE. unfold RCTX in Ha. lia.
  - constructor.
  - lia.
  - unfold K0U. lia.
  - unfold K0U. lia.
  - unfold B0U. lia.
  - unfold ps_init. cbn [ps_m]. rewrite pot_init. lia.
  - rewrite HRL. unfold K0U. lia.
  - rewrite RESV_eq. repeat constructor; cbv beta; apply Z.leb_le; vm_compute; reflexivity.
  - exact HLIM.
  - constructor.
Qed.

End INITU.
