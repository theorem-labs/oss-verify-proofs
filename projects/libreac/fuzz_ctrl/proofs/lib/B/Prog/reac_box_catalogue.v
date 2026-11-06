From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_box_catalogue_c.
Import ListNotations.
Open Scope Z_scope.

(* route (C): the proof below, formerly reac_box_catalogue_holds's, proves the region form
   reac_box_catalogue_contract_on (reac_box_catalogue_c.v); reac_box_catalogue_holds follows from it. *)
Theorem reac_box_catalogue_holds_on : reac_box_catalogue_contract_on.
Proof.
  unfold reac_box_catalogue_contract_on, REAC_BOX_CATALOGUE, REAC_BOX_CATALOGUE_FRAME, BOX_CATALOGUE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c lo
    -> ST HLO HCE HW Hpre.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (c, c + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  destruct (Z.eqb_spec c 0) as [E|E].
  - subst c.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU0.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step.
    rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb].
    step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU0 WVS)|].
    split; [exact ST|]. cbn [Z.eqb]. exact MU0.
  - destruct Hpre as [|(H8 & HWR & HD & HADR)]; [contradiction|].
    pose proof HWR as (HWl & HWh & _).
    pose proof (rt_shadow_rd m c 8 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m c 8 HADR) as HAD.
    pose proof (rt_rt3 m c 8 HADR) as H3.
    assert (WV : forall x, ~ outside [(bv_unsigned sp - 16, bv_unsigned sp); (c, c + 8)] x ->
                           wview rsegs m (wa x) <> None).
    { intros x Hx. destruct (rc_not_outside_cons _ _ _ _ Hx) as [Hx1|Hx1]; [exact (WVS x Hx1)|].
      destruct (rc_not_outside_cons _ _ _ _ Hx1) as [Hx2|Hx2]; [exact (rc_wv_wr rsegs m c 8 x HWR Hx2)|].
      destruct (rc_not_outside_nil x Hx2). }
    set (off := ASAN_K) in HRT, HSR, HAD, H3. clearbody off.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off c 8 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 off c 8 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 off c 8 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    step.
    rewrite (rcl_eqb c 0) by lia.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    step. step.
    rewrite (unsigned_lit c) by lia. rewrite rcl_land7. rewrite H8. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb negb].
    pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step.
    clear RG RC.
    step.
    rewrite (unsigned_lit c) by lia. rewrite rc_shr3.
    step.
    destruct (asan_shadow_read_at rsegs m1 off c 8 _ 0 (c / 8 + off) HSR1 ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k & RK & BK).
    pose proof (asan_check_8 rsegs m1 off c 8 0 k HAD1 H31 ltac:(lia) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; exact H8) BK) as K0.
    pose proof (rc_signed0_unsigned0 k K0) as K0u.
    step.
    clear RK.
    step.
    rewrite (rcl_zxb_eqb k 0) by lia. rewrite K0u. cbn [Z.eqb negb].
    pose proof (rcl_store_ok rsegs m1 c 8 8%nat HWR ltac:(lia)) as STc.
    step. step.
    change (Z_to_bv 64 c) with (wa c).
    pose proof (bytes_at_write_same rsegs m1 c (le8 (Z_to_bv 64 11)) ltac:(lia) ltac:(rewrite length_le8; lia))
      as HC.
    apply (rw_cells_frame rsegs m1 _ _ c (le8 (Z_to_bv 64 11))) in FR;
      [| lia | rewrite length_le8; lia | simpl_sizes; lia].
    apply (stk_write rsegs m1 lo _ c (le8 (Z_to_bv 64 11))) in ST; [| lia | rewrite length_le8; lia].
    apply (munch_write _ m m1 c (le8 (Z_to_bv 64 11))) in MU;
      [| lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia].
    apply (wmono_write rsegs m m1 (wa c) (le8 (Z_to_bv 64 11))) in WM.
    set (m2 := write_to_mem m1 (wa c) (le8 (Z_to_bv 64 11))) in *. clearbody m2.
    step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_munch rsegs _ m m2 HI MU WV)|].
    split; [exact ST | exact HC].
Qed.

Theorem reac_box_catalogue_holds : reac_box_catalogue_contract.
Proof. exact (reac_box_catalogue_contract_of_on reac_box_catalogue_holds_on). Qed.
