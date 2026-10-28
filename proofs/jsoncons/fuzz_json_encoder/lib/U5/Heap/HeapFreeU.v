(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* free of the ubsan heap: credit unchanged; the global conjuncts survive because free only shrinks the mappings. *)
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

Section FREEU.
Variable sptop : Z.
Variable SCFG : SpuriousCfg.
Hypothesis HALLOC : sc_alloc SCFG = false.
Hypothesis MBND : forall R : RunP, @model_bounds R.

Theorem HIU_free : free_spec (L0U sptop) SCFG (HIU sptop).
Proof.
  intros fx R M model LB cr A n K [HH HG] Hh Hl Hm HinLB R10 R4 RET SOK HK0 CONT.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK
                  & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & FITM).
  (* register literals in the shape of the code-walk lemmas *)
  pose proof (bv5_lit 1 ltac:(lia) I) as E1. pose proof (bv5_lit 2 ltac:(lia) I) as E2.
  pose proof (bv5_lit 4 ltac:(lia) I) as E4. pose proof (bv5_lit 10 ltac:(lia) I) as E10.
  rewrite <- E10 in R10. rewrite <- E4 in R4. rewrite <- E1 in RET, CONT. rewrite <- E2 in SOK, CONT.
  clear E1 E2 E4 E10.
  cbn [hl_tp L0U L0] in R4.
  change (srealizes rsegs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs)) model) K).
  (* the block (p, A, n) of the freed address *)
  assert (HinLB1 : In (A, n) (map blk_iv LBb)) by (rewrite <- ELB; exact HinLB).
  apply in_map_iff in HinLB1. destruct HinLB1 as [[[p A'] n'] [Ebb Hbb]].
  unfold blk_iv, blk_addr, blk_size in Ebb. cbn in Ebb. injection Ebb as -> ->.
  pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa.
  pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.
  destruct (stack_ok_stk sptop HCEIL M _ SOK) as (STK & LO & SPT & SPR).
  destruct (errno_cell_any M) as [errv ERR].
  assert (SLO : bv_unsigned (getr R (Z_to_bv 5 2)) - RALIGNED_STACK <= bv_unsigned (getr R (Z_to_bv 5 2)) - RFREE_STACK)
    by (unfold RALIGNED_STACK, RMALLOC_STACK, RFREE_STACK; lia).
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (vm_compute; reflexivity). exact ERR. }
  (* the code walk of free *)
  pose proof (implM_eqv_transfer rsegs _ _ _ _ _
    (rfree_spec_proof (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
       (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8))
       (getr R (Z_to_bv 5 9)) (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12))
       (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14)) (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16))
       (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20))
       (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
       (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28))
       (getr R (Z_to_bv 5 29)) (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31)) _ _ M s LBb p A n
       (bv_unsigned (getr R (Z_to_bv 5 2)) - RALIGNED_STACK) sptop errv HR Hbb AUX SPT STK LO SLO ERR' MI R4 R10)
    (@mkst_eqv_canon fx R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs))) as IMPL.
  unfold raw_free in IMPL. apply implM_mget_inv in IMPL. cbv beta in IMPL. apply implM_bind_inv in IMPL.
  assert (LIVEp : In (fst p) (ld_live L)).
  { apply (Permutation_in _ (Permutation_sym PL)). change (fst p) with (blk_slot (p, A, n)). apply in_map. exact Hbb. }
  eapply (embed_free rsegs SCFG RESV IMG_HI (cfree (ps_m s) (Some (fst p))) L (fun (_ : mled) (_ : mstate) => True)
            EVF 0 (fun cs' : mstate => pot cs' <= pot (ps_m s)) s _ _ model model (m_vmmaps model) K
            (cfree_contract_proof (ps_m s) L (fst p) CR LIVEp) (mb_free (MBND RUNp) (ps_m s) L (fst p) CR LIVEp)
            IMPL HKL (eq_sym (with_vmmaps_eta model)) Hh Hl Hm (vm_shrunk_refl (m_vmmaps model))).
  intros cs' s' ms' mo' L' HQ HCP _ HPOT HK' Emo' HS E1' E2' E3'.
  cbv beta in HQ. apply implM_mupd_only_inv in HQ.
  destruct HQ as (ms2 & Hms2 & ms1 & POST & EQV).
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                    & Ems1 & MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & HFA & HSO & HR').
  subst ms1.
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
  assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
  assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
  apply (srz_msteps rsegs SCFG ms' ms2 mo' K Hh' Hl' (cj_msteps_cat rsegs ms' ms2 Hms2)).
  rewrite Ems2. rewrite (ret_pc_ok _ RET).
  rewrite (lb_remove_lbrm LBb p A n NDs Hbb) in HPRES, HR'.
  assert (ELB2 : HeapIface.lb_remove A LB = map blk_iv (lbrm LBb (p, A, n))).
  { rewrite ELB. exact (lb_remove_corr LBb p A n NDs NDa Hbb). }
  assert (SUB : forall b, In b (lbrm LBb (p, A, n)) -> In b LBb).
  { intros b Hb. unfold lbrm in Hb. apply list_elem_of_In in Hb. apply list_elem_of_filter in Hb.
    destruct Hb as [_ Hb]. apply list_elem_of_In. exact Hb. }
  apply (CONT (ms_regs ms2) m' mo').
  - exact (regs_preserved_canon R (ms_regs ms2) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' REQ).
  - rewrite ELB2. split.
    + exact (heap_pres_core_of_cj sptop HCEIL (lbrm LBb (p, A, n)) _ M m' HPRES HDEEP HIMG STK' LO).
    + cbn [hl_segs hl_errno L0U L0].
      destruct ERR as [[_ B1] _]. destruct ERR2 as [[_ B2] _].
      rewrite R4 in B2.
      replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO in B2 by (vm_compute; reflexivity).
      pose proof (bytes_at_rdn rsegs m' RERRNO _ 0%nat 4%nat B2 ltac:(simpl; lia)) as D2.
      pose proof (bytes_at_rdn rsegs M RERRNO _ 0%nat 4%nat B1 ltac:(simpl; lia)) as D1.
      cbn [Z.of_nat] in D1, D2. rewrite Z.add_0_r in D1, D2. unfold wa in D1, D2.
      rewrite D1, D2. reflexivity.
  - exact Emo'.
  - rewrite ELB2.
    assert (GU' : GU cr (m_vmmaps mo')) by exact (GU_shrunk cr (m_vmmaps model) (m_vmmaps mo') HG HS).
    destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    split; [| exact GU'].
    exists RUNp, (set_m cs' s'), (set_live (ap_remove (fst p) (ld_live L')) L'), (lbrm LBb (p, A, n)), nc.
    splits.
    + exact HCEIL.
    + reflexivity.
    + exact HR'.
    + exact (creach_free (ps_m s) L (fst p) L' cs' CR LIVEp HCP).
    + cbn [ld_live set_live].
      rewrite (cpath_live HCP).
      rewrite (ap_remove_filter (fst p) (ld_live L) (Permutation_NoDup (Permutation_sym PL) NDs) LIVEp).
      rewrite map_blk_slot_lbrm.
      exact (filter_Permutation _ _ _ PL).
    + exact (KL2_set_live RESV IMG_HI L' (ap_remove (fst p) (ld_live L')) (ps_brk s') (m_vmmaps mo') HK').
    + exact MI'.
    + exact AUX'.
    + intros a Ha.
      pose proof (bv_unsigned_in_range _ a) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned a).
      change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
      rewrite (HIMG (bv_unsigned a)).
      * unfold wa. rewrite Z_to_bv_bv_unsigned. exact (REPL a Ha).
      * unfold RCTX in *; lia.
      * unfold RCTX in *; lia.
      * unfold RCTX, RERRNO in *; lia.
    + apply Forall_forall. intros b Hb.
      pose proof (SUB b Hb) as HbL.
      rewrite Forall_forall in BLK. destruct (BLK b HbL) as [Sz Def]. split; [exact Sz|].
      intros i Hi.
      destruct (RHEAP_block_range_proof s LBb M b HR HbL) as (Q1 & _ & _ & Q4 & _).
      pose proof (@KStep.alloc_ceiling_lt RUNp) as Hac.
      assert (HC : rclient_addr (lbrm LBb (p, A, n)) (bv_unsigned (getr R (Z_to_bv 5 2))) (blk_addr b + i)).
      { right; right. exists b. split; [exact Hb| lia]. }
      destruct (HPRES (blk_addr b + i) ltac:(lia) HC) as [E _].
      rewrite E. apply Def. exact Hi.
    + exact Hnc.
    + exact Hk.
    + exact Hfst.
    + exact Hsnd.
    + change (pot (ps_m (set_m cs' s'))) with (pot cs'). lia.
    + rewrite length_app in LEN |- *. rewrite S1. lia.
    + rewrite S1. apply Forall_app in FA. destruct FA as [FA1 FA2]. apply Forall_app. split; [exact FA1| exact (S4 FA2)].
    + rewrite S5. exact LIVE.
    + rewrite S5. rewrite Forall_forall in FITM |- *. intros x Hx. apply FITM. apply S7. exact Hx.
Qed.

End FREEU.
