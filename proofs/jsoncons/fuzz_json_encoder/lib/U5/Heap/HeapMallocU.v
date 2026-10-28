(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* malloc of the ubsan heap: requests 0 < n <= NBU with byte debit (malloc_u_spec); the small spec is its case n <= 2^27. *)
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

Section MALLOCU.
Variable sptop : Z.
Variable SCFG : SpuriousCfg.
Hypothesis HALLOC : sc_alloc SCFG = false.
Hypothesis MBND : forall R : RunP, @model_bounds R.

(* The bytes of a fresh block outside the image are defined in memory. *)
Lemma cb_defined : forall (m : word -> option byte) (A n : Z) (junk : list byte),
  rw_cells rsegs m A [CB (Z.to_nat n) junk] -> 0 <= A -> A + n < 2 ^ 63 -> (A + n <= 0x10000 \/ 0xfe000 <= A) ->
  forall i, 0 <= i < n -> m (wa (A + i)) <> None.
Proof.
  intros m A n junk [[[WF _] (_ & _ & BA)] _] HA HAn HR i Hi.
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. cbn [cell_wf] in WF.
  specialize (BA (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in BA by lia.
  rewrite ref_mrd_overlay in BA by (rewrite wa_unsigned by lia; lia).
  intro E. rewrite E in BA. symmetry in BA. apply nth_error_None in BA. lia.
Qed.

Theorem HIU_malloc_u : malloc_u_spec (L0U sptop) SCFG (HIU sptop).
Proof.
  intros fx R M model LB cr n K [HH HG] Hh Hl Hm R10 Hn [CRK CRB] R4 RET SOK HK0 CONT.
  change (KPM <= fst cr) in CRK. change (n + BOV <= snd cr) in CRB.
  rewrite <- (bv5_lit 10 ltac:(lia)) in R10. rewrite <- (bv5_lit 10 ltac:(lia)) in CONT.
  rewrite <- (bv5_lit 4 ltac:(lia)) in R4.
  rewrite <- (bv5_lit 2 ltac:(lia)) in SOK. rewrite <- (bv5_lit 2 ltac:(lia)) in CONT.
  rewrite <- (bv5_lit 1 ltac:(lia)) in RET. rewrite <- (bv5_lit 1 ltac:(lia)) in CONT.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK
                  & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & FITM).
  subst LB.
  destruct (stack_ok_stk sptop HCEIL M (bv_unsigned (getr R (Z_to_bv 5 2))) SOK) as (STK & LO & SPT & SPR).
  destruct (errno_cell_any M) as [errv ERR].
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 (hl_tp (L0U sptop))) + -164) with RERRNO by (vm_compute; reflexivity).
    exact ERR. }
  assert (Hn0 : 0 <= n) by lia.
  assert (Hn48 : 0 <= n < 2 ^ 48) by (unfold NBU in Hn; lia).
  pose proof (rmalloc_spec (RUNp:=RUNp)
    (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
    (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8))
    (getr R (Z_to_bv 5 9)) (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12))
    (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14)) (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16))
    (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20))
    (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
    (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28))
    (getr R (Z_to_bv 5 29)) (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
    (@fp_regs fx) (@fp_csr fx) M s LBb n (bv_unsigned (getr R (Z_to_bv 5 2)) - RALIGNED_STACK) sptop errv
    HR AUX SPT STK LO ltac:(unfold RALIGNED_STACK; lia) ERR' MI R4 R10 Hn48) as IMPL.
  pose proof (@implM_eqv_transfer _ _ _ _ _ _ _ (@mkst fx R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom rsegs)) IMPL
                (mkst_eqv_canon (fx:=fx) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom rsegs))) as IMPL1.
  unfold raw_malloc in IMPL1. apply implM_mget_inv in IMPL1. cbv beta in IMPL1. apply implM_bind_inv in IMPL1.
  assert (HPA : pot (ps_m s) + AMC <= POTMAX + AMC).
  { assert (HNC : nc <= NCMAX) by (rewrite K0_val, KPM_val in Hk; unfold NCMAX; lia).
    assert (HAMC : 0 <= AMC) by (apply Z.leb_le; vm_compute; reflexivity).
    pose proof (Z.mul_le_mono_nonneg_l nc NCMAX AMC HAMC HNC). unfold POTMAX. lia. }
  destruct (CALLB_le n (pot (ps_m s) + AMC) Hn0 HPA) as [CB0 CB1].
  eapply (embed (RUNp:=RUNp) rsegs SCFG HALLOC RESV IMG_HI (CAPKU cr)
            (live_bytes (vm_maps (m_vmmaps model)) + CALLB n (pot (ps_m s) + AMC)) (CAPKU_ok cr CRK)
            (cmalloc (ps_m s) n) L _ (elen_ok n (pot (ps_m s) + AMC)) EVM (CALLB n (pot (ps_m s) + AMC)) _ s _ _
            model model K
            (cmalloc_contract_proof (ps_m s) L n CR Hn0)
            (mb_malloc (MBND RUNp) (ps_m s) L n CR Hn0 (size_overflows_x n ltac:(lia)))
            (fun a len prot flags HE Hf Hp => elen_ok_NONEMAX n _ a len prot flags HPA HE Hf Hp)
            IMPL1 HKL (eq_sym (with_vmmaps_eta model)) Hh Hl Hm HK0
            (RIU_pre L (ps_brk s) (m_vmmaps model) cr n (pot (ps_m s) + AMC) HKL FA LIVE FITM HG
               ltac:(lia) CRB CRK HPA)).
  intros [cs' rc] s' ms' mo' L' HQm HCP HPost [HSOME HPOT] HK' Emo' HRI' Hps Hfa Hso.
  destruct rc as [c1|]; [|exfalso; apply HSOME; reflexivity].
  cbn [fst snd] in HPOT.
  cbv beta iota in HQm.
  apply implM_mupd_inv in HQm. apply implM_ret_inv in HQm.
  destruct HQm as (ms2 & Hms2 & ms1 & POST & EQV).
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                    & m' & errv' & Ems1 & MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _
                    & A & junk & EA0 & RBR & HR' & UCH & _).
  subst ms1. unfold rimg_pres in HIMG.
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
  assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
  assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
  eapply (srz_msteps rsegs SCFG ms' ms2 mo' K Hh' Hl' (cj_msteps_cat _ _ _ Hms2)).
  rewrite Ems2. rewrite (ret_pc_ok _ RET).
  pose proof (KStep.alloc_ceiling_lt (RUNp:=RUNp)) as ACL.
  destruct RBR as (B1 & B2 & B3 & B4 & B5).
  pose proof (block_ge_4096 (set_m cs' s') ((c1, fresh_off cs' c1 n, A, n) :: LBb) m' (c1, fresh_off cs' c1 n, A, n)
                HR' (or_introl eq_refl)) as HA4.
  change (4096 <= A) in HA4.
  pose proof (cb_defined m' A n junk UCH ltac:(lia) ltac:(lia) B5) as DEF.
  destruct (RIU_post sptop (m_vmmaps model) (m_vmmaps mo') cr n (pot (ps_m s) + AMC) HG CRB CRK HPA Hn0 HRI')
    as [HG' LEN'].
  pose proof HRI' as (Q1 & Q2 & Q3 & Q4 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  apply (CONT (ms_regs ms2) m' mo' A).
  - (* result register *)
    rewrite <- (getr_eqv _ _ (Z_to_bv 5 10) REQ). exact EA0.
  - exact (regs_preserved_canon R (ms_regs ms2) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' REQ).
  - (* block_range *)
    change (4096 <= A /\ (A + n <= 0x10000 \/ 0xfe000 <= A) /\ A mod 16 = 0 /\ 0 < n /\ A + n <= sptop - 2 ^ 23).
    lia.
  - (* blocks_apart *)
    intros b Hb. apply in_map_iff in Hb as (bb & Ebb & Hbb). subst b.
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NIN _].
    assert (Hid : blk_id (c1, fresh_off cs' c1 n, A, n) <> blk_id bb).
    { intro E. apply NIN. rewrite E. apply in_map. exact Hbb. }
    destruct (RHEAP_blocks_disjoint_proof _ _ _ _ _ HR' (or_introl eq_refl) (or_intror Hbb) Hid) as [D|D];
      destruct bb as [[bp ba] bs]; cbn [blk_iv blk_addr blk_size fst snd] in D |- *; lia.
  - (* defined *)
    intros i Hi. exact (DEF i Hi).
  - (* heap_pres_core *)
    exact (heap_pres_core_of_cj sptop HCEIL LBb (bv_unsigned (getr R (Z_to_bv 5 2))) M m' HPRES HDEEP HIMG STK' LO).
  - exact Emo'.
  - (* the invariant after the call *)
    assert (ED : debit (L0U sptop) cr n = (fst cr - KPM, snd cr - (n + BOV))) by reflexivity.
    rewrite ED in LEN' |- *. cbn [fst snd] in LEN'.
    split; [|exact HG'].
    exists RUNp, (set_m cs' s'), (set_live (c1 :: ld_live L') L'), ((c1, fresh_off cs' c1 n, A, n) :: LBb), (nc + 1).
    cbn [fst snd]. pose proof KPM_val as HKPM.
    splits.
    + exact HCEIL.
    + reflexivity.
    + exact HR'.
    + exact (creach_malloc (ps_m s) L n L' cs' (Some c1) CR Hn0 HCP).
    + change (Permutation (c1 :: ld_live L') (c1 :: map blk_slot LBb)).
      rewrite (cpath_live HCP). apply perm_skip. exact PL.
    + exact (KL2_set_live RESV IMG_HI L' (c1 :: ld_live L') (ps_brk s') (m_vmmaps mo') HK').
    + exact MI'.
    + exact AUX'.
    + intros a Ha. pose proof (wa_unsigned_id a) as Ea.
      rewrite <- Ea. rewrite HIMG.
      * rewrite Ea. apply REPL. exact Ha.
      * unfold RCTX in Ha. lia.
      * unfold RCTX in *. lia.
      * unfold RCTX, RERRNO in *. lia.
    + constructor.
      * cbn [blk_size blk_addr fst snd]. split; [lia|]. intros i Hi. exact (DEF i Hi).
      * apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BLK b Hb) as [Sz Def].
        split; [exact Sz|]. intros i Hi.
        destruct (RHEAP_block_range_proof _ _ _ _ HR Hb) as (R1 & R2 & R3 & R4' & R5).
        assert (HC : rclient_addr LBb (bv_unsigned (getr R (Z_to_bv 5 2))) (blk_addr b + i)).
        { right; right. exists b. split; [exact Hb| lia]. }
        destruct (HPRES (blk_addr b + i) ltac:(lia) HC) as [E _].
        rewrite E. apply Def. exact Hi.
    + lia.
    + lia.
    + lia.
    + lia.
    + change (pot cs' <= POT0 + AMC * (nc + 1)). lia.
    + exact LEN'.
    + exact Q2.
    + exact Q7.
    + exact Q8.
Qed.

Theorem HIU_malloc : malloc_spec (L0U sptop) SCFG (HIU sptop).
Proof. exact (malloc_spec_of_u (L0U sptop) SCFG (HIU sptop) NBU ltac:(unfold NBU; lia) HIU_malloc_u). Qed.

End MALLOCU.
