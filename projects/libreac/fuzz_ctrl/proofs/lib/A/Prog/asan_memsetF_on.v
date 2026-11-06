(* Proof of asan_memset_contract_F_on (asan_memset_cF_on.v): fuzz_ctrl's route (C) form of asan_memset_holds_F.
   The proof is asan_memsetF.v's asan_memset_holds_F (that file is UNCHANGED apart from comment text and its lemmas are reused), with the
   three places that consume `shadow_rw m` replaced, as in asan_memset_on.v: the destination's first and last
   shadow words come from qc_word_on (asan_memset_on.v), and the post's shadow presence from
   ShadowRwOnT.shadow_rw_on_kept, for any region the caller holds. Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge BzCallBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memset_c asan_memset_c asan_region_is_poisoned.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan asan_memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memsetF sh_word_on sh_word_on_bz asan_memset_c_on asan_memset_on asan_memset_cF_on.

Theorem asan_memset_holds_F_on : memset_contract -> asan_memset_contract_F_on.
Proof.
  intros MSC. unfold asan_memset_contract_F_on.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk lo.
  cbv zeta. intros HRW HN HA HE H7 HRT HSEP HST HK HLO HSP HC HSR HMI RB RI RF RD RSW _.
  pose proof HA as (HA0 & HA1 & HA2 & HAB).
  pose proof (sh_word_rng_sh RNG (bv_unsigned a0) (bv_unsigned a2) RB HA0 HA1
                ltac:(unfold APPMEM_END in HA2; lia) RSW) as RS.
  clear RSW.
  pose (P := PM (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2)).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) x
             ltac:(unfold IMG_LO, IMG_HI in Hx; lia) (or_introl Hx)). }
  assert (PF : forall x, bv_unsigned sp - ASAN_MEMSET_K <= x < bv_unsigned sp -> P (wa x) = true).
  { pose proof RF as (F0 & F1 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) x ltac:(lia) (or_intror (or_introl Hx))). }
  assert (PD : forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a2 -> P (wa x) = true).
  { pose proof RD as (D0 & D1 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_introl Hx)))). }
  assert (PS : forall x, sh_lo (bv_unsigned a0) <= x < sh_lo (bv_unsigned a0) + sh_len (bv_unsigned a0) (bv_unsigned a2) ->
            P (wa x) = true).
  { pose proof RS as (S0 & S1 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror Hx)))). }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { destruct (P (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) (2^64 - 1) ltac:(lia) E) as [X|[X|[X|X]]].
    - unfold IMG_LO, IMG_HI in X. lia.
    - unfold APPMEM_END in HSP. lia.
    - unfold APPMEM_END in HA2. lia.
    - pose proof (sh_top (bv_unsigned a0) (bv_unsigned a2) HA0 HA1 ltac:(unfold APPMEM_END in HA2; lia)). lia. }
  assert (S0 : MemNormP.in_seg rsegs (wa (2^64 - 1)) = false).
  { destruct (MemNormP.in_seg rsegs (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    pose proof (in_seg_img (2^64 - 1) ltac:(lia) E) as X. unfold IMG_LO, IMG_HI in X. lia. }
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) x Hx Hp) as [X|[X|[X|X]]].
      + destruct RI as (_ & _ & R). apply R; lia.
      + destruct RF as (_ & _ & R). apply R; lia.
      + destruct RD as (_ & _ & R). apply R; lia.
      + destruct RS as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs). apply R; lia. }
  apply (MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 S0 HB).
  clear HB P0 S0.
  unfold ASAN_MEMSET_K, end_in_app in *.
  pose proof (bv_unsigned_in_range 64 a1) as RC. unfold bv_modulus in RC. change (2 ^ Z.of_N 64) with (2 ^ 64) in RC.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 2208) (bv_unsigned sp) HST ltac:(lia)) as [STlo STw].
  apply (ExecF.evtF_mono rsegs (MemNormP.RNG_P rsegs P) (fun st => exists st0,
            BzAms.amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp - 2208)
              (MemNormP.normalize_P rsegs P m) st0
            /\ MemNormP.ms_rel_P rsegs P st st0 /\ MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzAms.amemset_spec BzP.rip_proof (memset_callZ_of_contract MSC)
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNormP.normalize_P rsegs P m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) junk
             (bv_unsigned sp - 2208)).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + refine (MemNormP.stk_P_of_cj rsegs P m (bv_unsigned sp - 2208) (bv_unsigned sp) _
                (stk_normalize m _ _ HMI STw ltac:(unfold TASK_SIZE, APPMEM_END in *; lia))).
      intros x Hx. left. apply PF. exact Hx.
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + destruct (Z.eq_dec (bv_unsigned a2) 0) as [E0|E0]; [left; exact E0|right]. lia.
    + apply (rw_cells_P P m).
      * intros i Hi. apply PD. cbn [BzCl.cells_size BzCl.csize] in Hi. lia.
      * apply rw_cb_normalize; [exact HMI | exact HRW | rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia].
    + split; [|split].
      * apply (acc_P P m); [|exact (acc_normalize m _ _ RO HA)].
        intros i Hi. apply PS. apply shad_in_sh; lia.
      * intros HN64.
        assert (AD : app_mem (bv_unsigned a0)).
        { destruct (HAB 0 ltac:(lia)) as [Ha _]. rewrite Z.add_0_r in Ha. exact Ha. }
        assert (ADN : app_mem (bv_unsigned a0 + bv_unsigned a2 - 1)).
        { destruct (HAB (bv_unsigned a2 - 1) ltac:(lia)) as [Ha _].
          replace (bv_unsigned a0 + bv_unsigned a2 - 1) with (bv_unsigned a0 + (bv_unsigned a2 - 1)) by lia. exact Ha. }
        assert (HNp : 0 < bv_unsigned a2) by lia.
        destruct (qc_word_on _ m _ HSR (fun i Hi => sh_word_on_cover _ _ HNp _ i (or_introl eq_refl) Hi)
                    HMI (fun i Hi => al8_shadow _ i AD Hi)) as (w1 & W1).
        destruct (qc_word_on _ m _ HSR (fun i Hi => sh_word_on_cover _ _ HNp _ i (or_intror eq_refl) Hi)
                    HMI (fun i Hi => al8_shadow _ i ADN Hi)) as (w2 & W2).
        exists w1, w2. split.
        -- apply (ro_cells_P P m); [|exact W1]. intros i Hi.
           change (Z.of_nat (BzCl.cells_size [BzCl.C8 w1])) with 8 in Hi.
           apply PS. apply al8_in_sh1; lia.
        -- apply (ro_cells_P P m); [|exact W2]. intros i Hi.
           change (Z.of_nat (BzCl.cells_size [BzCl.C8 w2])) with 8 in Hi.
           apply PS. apply al8_in_sh2; lia.
      * intros HN0. split; [|lia].
        assert (AD : app_mem (bv_unsigned a0)).
        { destruct (HAB 0 ltac:(lia)) as [Ha _]. rewrite Z.add_0_r in Ha. exact Ha. }
        assert (ADN : app_mem (bv_unsigned a0 + bv_unsigned a2)) by (destruct HE; [lia | assumption]).
        assert (AD7 : app_mem (bv_unsigned a0 + 7)) by (destruct H7; [lia | assumption]).
        unfold BzC.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
    + destruct (m2s_cells_normalize m HMI HC) as (M1 & M2 & M3).
      unfold BzR.m2s_cells. split; [|split];
        (apply (rw_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + destruct (icells_normalize m HMI HC) as (I1 & I2 & I3 & I4 & I5).
      unfold BzW.icells_ms. split; [|split; [|split; [|split]]];
        (apply (ro_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + apply BzM.mem_inv_intro; [exact seg_addr_below|].
      intros x b Hx. pose proof (normP_cj P m x b Hx) as Hc. pose proof (bz_mem_inv_normalize m) as BI.
      split; [exact (BzM.mem_inv_ro BzI.asegs _ x b BI Hc) | exact (BzM.mem_inv_ov_below BzI.asegs _ x b BI Hc)].
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2208, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply (MemNormP.munch_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st))
      by (eapply (MemNormP.wmono_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact WM]).
    assert (RW' : rw_cells rsegs (ms_mem st) (bv_unsigned a0)
                    [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))]).
    { apply rw_cb_of_bz in RW. destruct RW as [[Hwf Hb] Hw].
      split; [split; [exact Hwf | exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 Hb)]
             | exact (MemNormP.wr_at_rel_P rsegs P _ _ _ _ E8 Hw)]. }
    assert (AW : all_app [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2208, bv_unsigned sp)]).
    { split; [exact (addressable_app m _ _ HA)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. lia. }
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + rewrite Z_to_bv_bv_unsigned in E1.
      destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MU'.
    + exact WM'.
    + intros x b Hx. destruct (MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (HMI x b Hx).
    + apply (stk_merge rsegs _ lo (bv_unsigned sp - 2208) (bv_unsigned sp)); [| exact (stk_rel_P P _ _ _ _ E8 ST) | lia].
      apply (stk_kept _ m _ lo (bv_unsigned sp - 2208) STlo MU' WM').
      intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned a0)) as [L|L]; [left; cbn; lia|].
      destruct (Z_lt_le_dec x (bv_unsigned a0 + bv_unsigned a2)) as [L2|L2]; [right | left; cbn; lia].
      apply (rw_cb_mrd _ _ _ _ x RW'). rewrite Z2Nat.id by lia. lia.
    + exact RW'.
    + apply (asan_cells_kept _ m _ HC MU'). cbn. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    + intros Pq HPq. exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.shadow_rw_on_kept Pq m _ HPq (munch_meta _ m _ MU' AW) WM').
Qed.

Print Assumptions asan_memset_holds_F_on.
