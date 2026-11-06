(* Proof of asan_memset_contract_on (asan_memset_c_on.v): fuzz_ctrl's route (C) form of asan_memset_holds.
   The proof is asan_memset.v's asan_memset_holds (that file is UNCHANGED and its lemmas are reused), with the
   three places that consume `shadow_rw m` replaced:
     - the destination's first and last shadow words (asan_memset.v:139-140, qc_word) come from qc_word_on, which
       needs only those 8 bytes each (stk_in_shadow_on);
    - the post's shadow presence (asan_memset.v:181) comes from the form's ShadowRwOnT.shadow_rw_on_kept, for any region.
   Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge BzCallBridge ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memset_c asan_memset_c asan_region_is_poisoned.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset sh_word_on sh_word_on_bz asan_memset_c_on.
Import ListNotations.
Open Scope Z_scope.

(* asan_memset.v stk_in_shadow, from the region that holds the 8 bytes. *)
Lemma stk_in_shadow_on : forall (P : Z -> Prop) m x, shadow_rw_on P m -> (forall i, 0 <= i < 8 -> P (x + i)) ->
  (forall i, 0 <= i < 8 -> in_shadow (x + i)) -> stk rsegs m x (x + 8).
Proof.
  intros P m x H HP HS. pose proof (in_shadow_range _ (HS 0 ltac:(lia))). pose proof (in_shadow_range _ (HS 7 ltac:(lia))).
  split; [lia|]. split; [lia|]. intros a Ha.
  replace a with (x + (a - x)) by lia. exact (H _ (HP (a - x) ltac:(lia)) (HS (a - x) ltac:(lia))).
Qed.

(* asan_memset.v qc_word, from the region that holds the 8 bytes of the word. *)
Lemma qc_word_on : forall (P : Z -> Prop) m x, shadow_rw_on P m -> (forall i, 0 <= i < 8 -> P (x + i)) ->
  mem_inv rsegs m -> (forall i, 0 <= i < 8 -> in_shadow (x + i)) ->
  exists w, BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) x [BzCl.C8 w].
Proof.
  intros P m x HSR HP HMI HS.
  pose proof (in_shadow_task _ (HS 7 ltac:(lia))). pose proof (in_shadow_range _ (HS 0 ltac:(lia))).
  pose proof (stk_normalize m x (x + 8) HMI (stk_in_shadow_on P m x HSR HP HS) ltac:(lia)) as ST.
  destruct (stk_bytes rsegs _ x (x + 8) ST ltac:(lia)) as (bs & L & B).
  replace (Z.to_nat (x + 8 - x)) with 8%nat in L by lia.
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). apply ro_c8_to_bz. rewrite le8_of_bytes by exact L. exact B.
Qed.

Theorem asan_memset_holds_on : memset_contract -> asan_memset_contract_on.
Proof.
  intros MSC. unfold asan_memset_contract_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk lo.
  cbv zeta. intros HRW HN HA HE H7 HRT HSEP HST HK HLO HSP HC HSR HMI.
  unfold ASAN_MEMSET_K, end_in_app in *.
  pose proof (bv_unsigned_in_range 64 a1) as RC. unfold bv_modulus in RC. change (2 ^ Z.of_N 64) with (2 ^ 64) in RC.
  pose proof HA as (HA0 & HA1 & HA2 & HAB).
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL0.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 2208) (bv_unsigned sp) HST ltac:(lia)) as [STlo STw].
  apply (evt_mono rsegs (fun st => exists st0,
            BzAms.amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp - 2208) (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (evt_normalize_cj rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzAms.amemset_spec BzP.rip_proof (memset_callZ_of_contract MSC)
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) junk (bv_unsigned sp - 2208)).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (stk_normalize m _ _ HMI STw ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + destruct (Z.eq_dec (bv_unsigned a2) 0) as [E0|E0]; [left; exact E0|right]. lia.
    + apply rw_cb_normalize; [exact HMI | exact HRW | rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia].
    + split; [|split].
      * exact (acc_normalize m _ _ RO HA).
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
        exists w1, w2. split; assumption.
      * intros HN0. split; [|lia].
        assert (AD : app_mem (bv_unsigned a0)).
        { destruct (HAB 0 ltac:(lia)) as [Ha _]. rewrite Z.add_0_r in Ha. exact Ha. }
        assert (ADN : app_mem (bv_unsigned a0 + bv_unsigned a2)) by (destruct HE; [lia | assumption]).
        assert (AD7 : app_mem (bv_unsigned a0 + 7)) by (destruct H7; [lia | assumption]).
        unfold BzC.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
    + exact (m2s_cells_normalize m HMI HC).
    + exact (icells_normalize m HMI HC).
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2208, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st)) by (eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM]).
    assert (RW' : rw_cells rsegs (ms_mem st) (bv_unsigned a0)
                    [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))])
      by exact (rw_cb_of_normalized _ _ _ _ _ E8 RW).
    assert (AW : all_app [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2208, bv_unsigned sp)]).
    { split; [exact (addressable_app m _ _ HA)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. lia. }
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + rewrite Z_to_bv_bv_unsigned in E1.
      destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MU'.
    + exact WM'.
    + exact (mem_inv_of_normalized m _ HMI SAME).
    + apply (stk_merge rsegs _ lo (bv_unsigned sp - 2208) (bv_unsigned sp)); [| exact (stk_of_normalized _ _ _ _ E8 ST) | lia].
      apply (stk_kept _ m _ lo (bv_unsigned sp - 2208) STlo MU' WM').
      intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned a0)) as [L|L]; [left; cbn; lia|].
      destruct (Z_lt_le_dec x (bv_unsigned a0 + bv_unsigned a2)) as [L2|L2]; [right | left; cbn; lia].
      apply (rw_cb_mrd _ _ _ _ x RW'). rewrite Z2Nat.id by lia. lia.
    + exact RW'.
    + apply (asan_cells_kept _ m _ HC MU'). cbn. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    + intros P HP.
      exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.shadow_rw_on_kept P m _ HP (munch_meta _ m _ MU' AW) WM').
Qed.

Print Assumptions asan_memset_holds_on.
