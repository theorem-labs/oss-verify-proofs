(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* aligned_alloc(16, n) of the ubsan heap, n <= 2^27, byte debit. *)
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

Section ALIGNEDU.
Variable sptop : Z.
Variable SCFG : SpuriousCfg.
Hypothesis HALLOC : sc_alloc SCFG = false.
Hypothesis MBND : forall R : RunP, @model_bounds R.

Theorem HIU_aligned : aligned_alloc16_spec (L0U sptop) SCFG (HIU sptop).
Proof.
  intros fx R M model LB cr n K [HH HG] Hh Hl Hm R10 R11 Hn HCR R4 RET SOK HK0 CONT.
  rewrite <- (bv5_lit 10 ltac:(lia) I) in R10, CONT.
  rewrite <- (bv5_lit 11 ltac:(lia) I) in R11.
  rewrite <- (bv5_lit 4 ltac:(lia) I) in R4.
  rewrite <- (bv5_lit 1 ltac:(lia) I) in RET, CONT.
  rewrite <- (bv5_lit 2 ltac:(lia) I) in SOK, CONT.
  destruct HCR as [CRK CRB].
  change (hl_k_per_malloc (L0U sptop)) with KPM in CRK.
  change (hl_b_overhead (L0U sptop)) with BOV in CRB.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK
                  & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & FITM).
  destruct (@stack_ok_stk sptop RUNp HCEIL M _ SOK) as (STK & LO & SPT & SPR).
  destruct (errno_cell_any M) as [errv ERR].
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 (hl_tp (L0U sptop))) + -164) with RERRNO; [exact ERR|].
    vm_compute. reflexivity. }
  pose proof (repl_cells M REPL) as REPL'.
  pose proof (@raligned_spec RUNp
    (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
    (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8))
    (getr R (Z_to_bv 5 9)) (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12))
    (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14)) (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16))
    (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20))
    (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
    (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28))
    (getr R (Z_to_bv 5 29)) (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
    (@fp_regs fx) (@fp_csr fx) M s LBb n (bv_unsigned (getr R (Z_to_bv 5 2)) - RALIGNED_STACK) sptop errv
    HR AUX SPT STK LO ltac:(lia) ERR' MI R4 REPL' R10 R11 ltac:(lia)) as IMPL.
  pose proof (@implM_eqv_transfer rsegs _ _ _ _ _ _ _ IMPL
                (@mkst_eqv_canon fx R (Z_to_bv 64 RAA_SYM) M (seg_rom rsegs))) as IMPL1.
  pose proof (@implM_mget_inv rsegs _ _ _ _ _ _ IMPL1) as IMPL2.
  pose proof (@implM_bind_inv rsegs _ _ _ _ _ _ _ _ IMPL2) as IMPL3.
  clear IMPL IMPL1 IMPL2.
  assert (HPA : pot (ps_m s) + AMC <= POTMAX + AMC).
  { clear - Hk CRK POT. rewrite KPM_val in Hk, CRK. rewrite K0_val in Hk. unfold POTMAX, NCMAX, AMC in *. lia. }
  destruct (CALLB_le n (pot (ps_m s) + AMC) ltac:(lia) HPA) as [CB0 CB1].
  assert (HRI : RI (CAPKU cr) (live_bytes (vm_maps (m_vmmaps model)) + CALLB n (pot (ps_m s) + AMC)) EVM
                   (CALLB n (pot (ps_m s) + AMC)) (m_vmmaps model)).
  { eapply RIU_pre; [exact HKL | exact FA | exact LIVE | exact FITM | exact HG | unfold NBU; lia
                    | exact CRB | exact CRK | exact HPA]. }
  change (hl_segs (L0U sptop)) with rsegs.
  change (hl_aligned_alloc (L0U sptop)) with RAA_SYM.
  eapply (@embed RUNp rsegs SCFG HALLOC RESV IMG_HI (CAPKU cr)
            (live_bytes (vm_maps (m_vmmaps model)) + CALLB n (pot (ps_m s) + AMC)) (CAPKU_ok cr CRK)
            _ (@cmalloc RUNp (ps_m s) n) L _ (elen_ok n (pot (ps_m s) + AMC)) EVM (CALLB n (pot (ps_m s) + AMC)) _
            s _ _ model model K
            (@cmalloc_contract_proof RUNp (ps_m s) L n CR ltac:(lia))
            (@mb_malloc RUNp (MBND RUNp) (ps_m s) L n CR ltac:(lia) (size_overflows_small n ltac:(lia)))
            (fun a len prot flags HE Hf Hp => elen_ok_NONEMAX n (pot (ps_m s) + AMC) a len prot flags HPA HE Hf Hp)
            IMPL3 HKL (eq_sym (with_vmmaps_eta model)) Hh Hl Hm HK0 HRI).
  intros [cs' rc] s' ms' mo' L' HQ HCP HPOST [HSOME HPOT] HK' Emo' HRI' E1 E2 E3.
  destruct rc as [c'1|]; [|exfalso; apply HSOME; reflexivity].
  cbn [fst snd] in HPOT.
  cbv beta iota in HQ.
  apply implM_mupd_inv in HQ. apply implM_ret_inv in HQ.
  destruct HQ as (ms2 & Hms2 & ms1 & [POST FIT] & EQV).
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv'
                    & Ems1 & MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & A & junk & EA0 & RBR & HR' & UCH & _).
  subst ms1.
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
  assert (Hh' : m_halted mo' = None) by (rewrite Emo'; exact Hh).
  assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
  eapply (srz_msteps rsegs SCFG ms' ms2 mo' K Hh' Hl' (cj_msteps_cat rsegs ms' ms2 Hms2)).
  rewrite Ems2, (ret_pc_ok _ RET).
  pose proof (@creach_malloc RUNp (ps_m s) L n L' cs' (Some c'1) CR ltac:(lia) HCP) as CR'.
  pose proof (@KL2_set_live RUNp RESV IMG_HI L' (c'1 :: ld_live L') (ps_brk s') (m_vmmaps mo') HK') as HK''.
  pose proof (@block_ge_4096 RUNp (set_m cs' s') _ m' _ HR' (or_introl eq_refl)) as HA4.
  cbn [blk_addr] in HA4.
  destruct RBR as (B1 & B2 & B3 & B4 & B5).
  pose proof (@KStep.alloc_ceiling_lt RUNp) as ACL.
  assert (DEF : forall i, 0 <= i < n -> m' (wa (A + i)) <> None).
  { intros i Hi. destruct UCH as [[WF BA] _]. destruct WF as [Hlen _].
    destruct BA as (BA0 & BA1 & BA2).
    change (cells_bytes [CB (Z.to_nat n) junk]) with (junk ++ []) in BA2.
    rewrite app_nil_r in BA2.
    assert (Hi' : (Z.to_nat i < length junk)%nat).
    { rewrite Hlen. apply Z2Nat.inj_lt; lia. }
    specialize (BA2 _ Hi').
    rewrite Z2Nat.id in BA2 by lia.
    rewrite ref_mrd_overlay in BA2 by (rewrite wa_unsigned by lia; lia).
    rewrite BA2. destruct (nth_error junk (Z.to_nat i)) eqn:E; [discriminate|].
    apply nth_error_None in E. rewrite Hlen in E. apply (Z2Nat.inj_le n i) in E; lia. }
  apply (CONT (ms_regs ms2) m' mo' A).
  - rewrite <- (getr_eqv _ _ (Z_to_bv 5 10) REQ). exact EA0.
  - exact (regs_preserved_canon R (ms_regs ms2) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' REQ).
  - split; [exact HA4|]. split; [exact B5|]. split; [exact B2|]. split; [lia|].
    change (hl_sptop (L0U sptop)) with sptop. rewrite HCEIL in B4. lia.
  - intros b Hb. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb).
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND.
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [Hni _].
    assert (Hid : blk_id (c'1, fresh_off cs' c'1 n, A, n) <> blk_id bb).
    { intro E. apply Hni. rewrite E. apply in_map. exact Hbb. }
    destruct (RHEAP_blocks_disjoint_proof _ _ _ _ _ HR' (or_introl eq_refl) (or_intror Hbb) Hid) as [D|D];
      change (blk_addr (c'1, fresh_off cs' c'1 n, A, n)) with A in D;
      change (blk_size (c'1, fresh_off cs' c'1 n, A, n)) with n in D;
      unfold blk_iv; cbn [fst snd]; lia.
  - exact DEF.
  - rewrite ELB. exact (@heap_pres_core_of_cj sptop RUNp HCEIL LBb _ M m' HPRES HDEEP HIMG STK' LO).
  - exact Emo'.
  - destruct (RIU_post sptop (m_vmmaps model) (m_vmmaps mo') cr n (pot (ps_m s) + AMC) HG CRB CRK HPA
                ltac:(lia) HRI') as [HG' LEN'].
    split; [| exact HG'].
    destruct HRI' as (Q1 & Q2 & Q3 & Q4 & Q6 & Q7 & Q8 & _).
    exists RUNp, (set_m cs' s'), (set_live (c'1 :: ld_live L') L'), ((c'1, fresh_off cs' c'1 n, A, n) :: LBb), (nc + 1).
    splits.
    + exact HCEIL.
    + rewrite ELB. reflexivity.
    + exact HR'.
    + exact CR'.
    + pose proof HCP as EL. apply cpath_live in EL.
      change (Permutation (c'1 :: ld_live L') (c'1 :: map blk_slot LBb)).
      rewrite EL. apply perm_skip. exact PL.
    + exact HK''.
    + exact MI'.
    + exact AUX'.
    + intros a Ha.
      assert (E : m' (wa (bv_unsigned a)) = M (wa (bv_unsigned a))).
      { pose proof (bv_unsigned_in_range 64 a) as Ra. apply HIMG; clear - Ha; unfold RCTX, RERRNO in *; lia. }
      unfold wa in E. rewrite !Z_to_bv_bv_unsigned in E. rewrite E. apply REPL. exact Ha.
    + constructor.
      * split; [cbn; lia | exact DEF].
      * apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BLK b Hb) as [Sz Def].
        split; [exact Sz|]. intros i Hi.
        destruct (RHEAP_block_range_proof _ _ _ _ HR Hb) as (W1 & W2 & W3 & W4 & W5).
        assert (CA : rclient_addr LBb (bv_unsigned (getr R (Z_to_bv 5 2))) (blk_addr b + i)).
        { right; right. exists b. split; [exact Hb | lia]. }
        destruct (HPRES (blk_addr b + i) ltac:(lia) CA) as [EM _].
        rewrite EM. apply Def. exact Hi.
    + lia.
    + unfold debit. cbn [fst snd]. change (hl_k_per_malloc (L0U sptop)) with KPM.
      clear - Hk. rewrite KPM_val in *. lia.
    + unfold debit. cbn [fst snd]. change (hl_k_per_malloc (L0U sptop)) with KPM. lia.
    + unfold debit. cbn [fst snd]. change (hl_b_overhead (L0U sptop)) with BOV. lia.
    + change (ps_m (set_m cs' s')) with cs'. clear - HPOT POT. unfold AMC in *. lia.
    + exact LEN'.
    + exact Q2.
    + exact Q7.
    + exact Q8.
Qed.

End ALIGNEDU.
