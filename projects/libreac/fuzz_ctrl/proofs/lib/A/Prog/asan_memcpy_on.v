(* Proof of asan_memcpy_contract_on (asan_memcpy_c_on.v): fuzz_ctrl's route (C) form of asan_memcpy_holds.
   The proof is asan_memcpy.v's asan_memcpy_holds (that file's code is UNCHANGED and its lemmas are reused), with the
   three places that consume `shadow_rw m` replaced:
     - the source's and the destination's chk_ok (asan_memcpy.v:280-281) come from chk_ok_of_ours_on, which reads
       only the aligned shadow word of the first and of the last byte of the range (shadow_word_on);
    - the post's shadow presence (asan_memcpy.v:304) comes from the form's ShadowRwOnT.shadow_rw_on_kept
      (AsanRTFacts.shadow_rw_kept restricted to a region), for any region the caller holds.
   Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c asan_memcpy sh_word_on sh_word_on_bz asan_memcpy_c_on.
Import ListNotations.
Open Scope Z_scope.

(* asan_memcpy.v shadow_word, from the region that holds the 8 bytes of x's aligned shadow word. *)
Lemma shadow_word_on : forall (P : Z -> Prop) m x, mem_inv rsegs m -> shadow_rw_on P m ->
  (forall j, 0 <= j < 8 -> P (BzQ.al8 (BzS.shad x) + j)) -> app_mem x ->
  exists w, BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) (BzQ.al8 (BzS.shad x)) [BzCl.C8 w].
Proof.
  intros P m x HMI HSR HP Hx. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  assert (HA : forall j, 0 <= j < 8 -> in_shadow (BzQ.al8 (BzS.shad x) + j)).
  { intros j Hj. unfold BzQ.al8, BzS.shad, BzS.SHB, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx.
    Z.div_mod_to_equations. destruct Hx as [Hx|Hx]; [left|right]; lia. }
  pose proof (in_shadow_range _ (HA 0 ltac:(lia))) as R0.
  pose proof (HA 7 ltac:(lia)) as R7.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in R7.
  destruct (bytes_exist m 8 (BzQ.al8 (BzS.shad x)) ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (bs & L & B).
  { intros j Hj. change (Z.of_nat 8) with 8 in Hj. destruct (HSR _ (HP j Hj) (HA j Hj)) as [_ Hb]. exact Hb. }
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [cbn; tauto|].
  assert (E : BzCl.cells_bytes [BzCl.C8 (Z_to_bv 64 (bytes_le_to_Z bs))] = bs).
  { cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact (le8_of_len8 bs L). }
  rewrite E.
  assert (HL : BzQ.al8 (BzS.shad x) + Z.of_nat (length bs) <= TASK_SIZE)
    by (rewrite L; change (Z.of_nat 8) with 8; unfold TASK_SIZE; lia).
  exact (bytes_normalize_low m _ bs RO HL B).
Qed.

(* asan_memcpy.v chk_ok_of_ours, from the region that holds the first and the last byte's aligned shadow words. *)
Lemma chk_ok_of_ours_on : forall (P : Z -> Prop) m p n, mem_inv rsegs m -> shadow_rw_on P m ->
  (0 < n -> forall x j, (x = p \/ x = p + n - 1) -> 0 <= j < 8 -> P (BzQ.al8 (BzS.shad x) + j)) ->
  addressable m p n -> end_in_app p n ->
  (n = 0 \/ app_mem (p + 7)) -> n <= 2^40 -> BzQ.chk_ok (normalize_cj rsegs m) p n.
Proof.
  intros P m p n HMI HSR HP AD EA A7 HN. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  split; [exact (acc_normalize m p n RO AD)|]. split.
  - intros Hn. pose proof AD as (P0 & N0 & PE & H).
    destruct (H 0 ltac:(lia)) as (A0 & _). destruct (H (n - 1) ltac:(lia)) as (A1 & _).
    rewrite Z.add_0_r in A0. replace (p + (n - 1)) with (p + n - 1) in A1 by lia.
    destruct (shadow_word_on P m p HMI HSR (fun j Hj => HP ltac:(lia) p j (or_introl eq_refl) Hj) A0) as [w1 W1].
    destruct (shadow_word_on P m (p + n - 1) HMI HSR (fun j Hj => HP ltac:(lia) (p + n - 1) j (or_intror eq_refl) Hj) A1)
      as [w2 W2].
    exists w1, w2. split; assumption.
  - exact (rng_of_ours m p n AD EA A7 HN).
Qed.

Theorem asan_memcpy_holds_on : asan_memcpy_contract_on.
Proof.
  unfold asan_memcpy_contract_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk lo.
  cbv zeta. intros SRC LEN DST OV HN AS AD ES ED H7 HRT HSD HSS HST HK HLO HSP HC HSR HMI.
  unfold ASAN_MEMCPY_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL0.
  pose proof AS as (S0 & N0 & SE & _). pose proof AD as (D0 & _ & DE & _).
  assert (EN : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  assert (S7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  assert (D7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  apply (evt_mono rsegs (fun st => exists st0,
            BzA.amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) src lo
              (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (evt_normalize_cj rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzA.amemcpy_spec BzP.rip_proof mc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) src junk lo); rewrite ?EN.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
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
      exact (bytes_normalize_low m (bv_unsigned a1) src RO HL SRC).
    + rewrite LEN.
      assert (HL : bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned a2)) <= TASK_SIZE)
        by (rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia).
      exact (rw_cb_normalize m (bv_unsigned a0) (Z.to_nat (bv_unsigned a2)) junk HMI HL DST).
    + exact (chk_ok_of_ours_on _ m (bv_unsigned a1) (bv_unsigned a2) HMI HSR
               (fun Hn x j Hx Hj => or_introl (sh_word_on_cover _ _ Hn x j Hx Hj)) AS ES S7 HN).
    + exact (chk_ok_of_ours_on _ m (bv_unsigned a0) (bv_unsigned a2) HMI HSR
               (fun Hn x j Hx Hj => or_intror (sh_word_on_cover _ _ Hn x j Hx Hj)) AD ED D7 HN).
    + exact (BCB.m2s_cells_normalize m HMI HC).
    + exact (icells_normalize m HMI HC).
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW & B).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    rewrite EN in MU. rewrite LEN in RW.
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2224, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st)) by (eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM]).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [|split; [|split; [|split; [|split]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + exact (mem_inv_of_normalized m _ HMI SAME).
    + exact (stk_of_normalized _ _ lo _ E8 ST).
    + exact (rw_cb_of_normalized _ _ _ _ _ E8 RW).
    + exact (bytes_at_rel_cj rsegs _ _ _ _ E8 B).
    + apply (asan_cells_kept _ m _ HC MU'). cbn [disjoint_from].
      split; [|split; [|exact I]]; unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia.
    + intros P HP. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.shadow_rw_on_kept P m _ HP); [|exact WM'].
      apply (munch_meta _ m _ MU'). cbn [all_app].
      split; [exact (addressable_app m _ _ AD)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
Qed.

Print Assumptions asan_memcpy_holds_on.
