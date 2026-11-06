(* Proof of asan_memcpy_contract_F_on (asan_memcpy_cF_on.v): fuzz_ctrl's route (C) form of asan_memcpy_holds_F.
   The proof is asan_memcpyF.v's asan_memcpy_holds_F (that file is UNCHANGED apart from comment text and its lemmas are reused), with the
   three places that consume `shadow_rw m` replaced, as in asan_memcpy_on.v: the source's and the destination's
   chk_ok come from chk_ok_of_ours_on (asan_memcpy_on.v), and the post's shadow presence from
   ShadowRwOnT.shadow_rw_on_kept, for any region the caller holds. Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c rng_asan asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset.
Import ListNotations.
Open Scope Z_scope.
Module AMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpyF sh_word_on sh_word_on_bz asan_memcpy_c_on asan_memcpy_on asan_memcpy_cF_on.

Theorem asan_memcpy_holds_F_on : asan_memcpy_contract_F_on.
Proof.
  unfold asan_memcpy_contract_F_on.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m src junk lo.
  cbv zeta. intros SRC LEN DST OV HN AS AD ES ED H7 HRT HSD HSS HST HK HLO HSP HC HSR HMI
    RB RI RF RDD RSS RSWD RSWS _.
  pose proof AS as (S0 & N0 & SE & _). pose proof AD as (D0 & _ & DE & _).
  pose proof (sh_word_rng_sh RNG (bv_unsigned a0) (bv_unsigned a2) RB D0 N0
                ltac:(unfold APPMEM_END in DE; lia) RSWD) as RSHD.
  pose proof (sh_word_rng_sh RNG (bv_unsigned a1) (bv_unsigned a2) RB S0 N0
                ltac:(unfold APPMEM_END in SE; lia) RSWS) as RSHS.
  clear RSWD RSWS.
  pose (P := PM (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x
             ltac:(unfold IMG_LO, IMG_HI in Hx; lia) (or_introl Hx)). }
  assert (PF : forall x, bv_unsigned sp - ASAN_MEMCPY_K <= x < bv_unsigned sp -> P (wa x) = true).
  { pose proof RF as (F0 & F1 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_introl Hx))). }
  assert (PD : forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a2 -> P (wa x) = true).
  { pose proof RDD as (D1 & D2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_introl Hx)))). }
  assert (PS : forall x, bv_unsigned a1 <= x < bv_unsigned a1 + bv_unsigned a2 -> P (wa x) = true).
  { pose proof RSS as (S1 & S2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_introl Hx))))). }
  assert (PSD : forall x, sh_lo (bv_unsigned a0) <= x < sh_lo (bv_unsigned a0) + sh_len (bv_unsigned a0) (bv_unsigned a2) ->
            P (wa x) = true).
  { pose proof RSHD as (H1 & H2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_intror (or_introl Hx)))))). }
  assert (PSS : forall x, sh_lo (bv_unsigned a1) <= x < sh_lo (bv_unsigned a1) + sh_len (bv_unsigned a1) (bv_unsigned a2) ->
            P (wa x) = true).
  { pose proof RSHS as (H1 & H2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_intror (or_intror Hx)))))). }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { destruct (P (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (2^64 - 1) ltac:(lia) E)
      as [X|[X|[X|[X|[X|X]]]]].
    - unfold IMG_LO, IMG_HI in X. lia.
    - unfold APPMEM_END in HSP. lia.
    - unfold APPMEM_END in DE. lia.
    - unfold APPMEM_END in SE. lia.
    - pose proof (sh_top (bv_unsigned a0) (bv_unsigned a2) D0 N0 ltac:(unfold APPMEM_END in DE; lia)). lia.
    - pose proof (sh_top (bv_unsigned a1) (bv_unsigned a2) S0 N0 ltac:(unfold APPMEM_END in SE; lia)). lia. }
  assert (G0 : MemNormP.in_seg rsegs (wa (2^64 - 1)) = false).
  { destruct (MemNormP.in_seg rsegs (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    pose proof (in_seg_img (2^64 - 1) ltac:(lia) E) as X. unfold IMG_LO, IMG_HI in X. lia. }
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x Hx Hp)
        as [X|[X|[X|[X|[X|X]]]]].
      + destruct RI as (_ & _ & R). apply R; lia.
      + destruct RF as (_ & _ & R). apply R; lia.
      + destruct RDD as (_ & _ & R). apply R; lia.
      + destruct RSS as (_ & _ & R). apply R; lia.
      + destruct RSHD as (_ & _ & R). apply R; lia.
      + destruct RSHS as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs). apply R; lia. }
  apply (MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 G0 HB).
  clear HB P0 G0.
  unfold ASAN_MEMCPY_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 2224) (bv_unsigned sp) HST ltac:(lia)) as [STlo STw].
  assert (EN : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  assert (S7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  assert (D7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  apply (ExecF.evtF_mono rsegs (MemNormP.RNG_P rsegs P) (fun st => exists st0,
            BzA.amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) src
              (bv_unsigned sp - 2224) (MemNormP.normalize_P rsegs P m) st0
            /\ MemNormP.ms_rel_P rsegs P st st0 /\ MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzA.amemcpy_spec BzP.rip_proof mc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (MemNormP.normalize_P rsegs P m) (bv_unsigned a0) (bv_unsigned a1) src junk
             (bv_unsigned sp - 2224)); rewrite ?EN.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + refine (MemNormP.stk_P_of_cj rsegs P m (bv_unsigned sp - 2224) (bv_unsigned sp) _
                (stk_normalize m _ _ HMI STw ltac:(unfold TASK_SIZE, APPMEM_END in *; lia))).
      intros x Hx. left. apply PF. exact Hx.
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + exact D0.
    + exact S0.
    + unfold APPMEM_END in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + right. exact HSS.
    + right. exact HSD.
    + assert (HL : bv_unsigned a1 + Z.of_nat (length src) <= TASK_SIZE)
        by (rewrite EN; unfold TASK_SIZE, APPMEM_END in *; lia).
      refine (MemNormP.bytes_at_P_of_cj rsegs P m (bv_unsigned a1) src _ (bytes_normalize_low m (bv_unsigned a1) src RO HL SRC)).
      intros i Hi. left. apply PS. lia.
    + rewrite LEN.
      assert (HL : bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned a2)) <= TASK_SIZE)
        by (rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia).
      apply (rw_cells_P P m).
      * intros i Hi. apply PD. cbn [BzCl.cells_size BzCl.csize] in Hi. lia.
      * exact (rw_cb_normalize m (bv_unsigned a0) (Z.to_nat (bv_unsigned a2)) junk HMI HL DST).
    + apply (chk_ok_P P m); [exact S0 | exact PSS |].
      exact (chk_ok_of_ours_on _ m (bv_unsigned a1) (bv_unsigned a2) HMI HSR
        (fun Hn x j Hx Hj => or_introl (sh_word_on_cover _ _ Hn x j Hx Hj)) AS ES S7 HN).
    + apply (chk_ok_P P m); [exact D0 | exact PSD |].
      exact (chk_ok_of_ours_on _ m (bv_unsigned a0) (bv_unsigned a2) HMI HSR
        (fun Hn x j Hx Hj => or_intror (sh_word_on_cover _ _ Hn x j Hx Hj)) AD ED D7 HN).
    + destruct (BCB.m2s_cells_normalize m HMI HC) as (M1 & M2 & M3).
      unfold BzR.m2s_cells. split; [|split];
        (apply (rw_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + destruct (icells_normalize m HMI HC) as (I1 & I2 & I3 & I4 & I5).
      unfold BzW.icells. split; [|split; [|split; [|split]]];
        (apply (ro_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + apply BzM.mem_inv_intro; [exact seg_addr_below|].
      intros x b Hx. pose proof (normP_cj P m x b Hx) as Hc. pose proof (bz_mem_inv_normalize m) as BI.
      split; [exact (BzM.mem_inv_ro BzI.asegs _ x b BI Hc) | exact (BzM.mem_inv_ov_below BzI.asegs _ x b BI Hc)].
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW & B).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    rewrite EN in MU. rewrite LEN in RW.
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2224, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply (MemNormP.munch_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st))
      by (eapply (MemNormP.wmono_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact WM]).
    assert (RW' : rw_cells rsegs (ms_mem st) (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]).
    { apply rw_cb_of_bz in RW. destruct RW as [[Hwf Hb] Hw].
      split; [split; [exact Hwf | exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 Hb)]
             | exact (MemNormP.wr_at_rel_P rsegs P _ _ _ _ E8 Hw)]. }
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + rewrite Z_to_bv_bv_unsigned in E1.
      destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MU'.
    + exact WM'.
    + intros x b Hx. destruct (MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (HMI x b Hx).
    + apply (stk_merge rsegs _ lo (bv_unsigned sp - 2224) (bv_unsigned sp)); [| exact (stk_rel_P P _ _ _ _ E8 ST) | lia].
      apply (AMS.stk_kept _ m _ lo (bv_unsigned sp - 2224) STlo MU' WM').
      intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned a0)) as [L|L]; [left; cbn; lia|].
      destruct (Z_lt_le_dec x (bv_unsigned a0 + bv_unsigned a2)) as [L2|L2]; [right | left; cbn; lia].
      apply (AMS.rw_cb_mrd _ _ _ _ x RW'). rewrite Z2Nat.id by lia. lia.
    + exact RW'.
    + exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 B).
    + apply (asan_cells_kept _ m _ HC MU'). cbn [disjoint_from].
      split; [|split; [|exact I]]; unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia.
    + intros Pq HPq. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.shadow_rw_on_kept Pq m _ HPq); [|exact WM']. apply (munch_meta _ m _ MU'). cbn [all_app].
      split; [exact (addressable_app m _ _ AD)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
Qed.

Print Assumptions asan_memcpy_holds_F_on.
