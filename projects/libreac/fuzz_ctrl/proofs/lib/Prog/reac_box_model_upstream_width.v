From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib reac_box_model_upstream_width_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uw_zero mp bs :=
  apply evt_done; hnf;
  replace (bm_uw mp bs) with 0 by (symmetry; unfold bm_uw, bm_wok; decide_tests; reflexivity);
  do 4 eexists; reflexivity.

Section W.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp : Z) (bs : list byte).

  Definition Qw : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs)) a1' a2' a3' a4' a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs).

  Lemma w_max : forall x0 x2 x3 x4,
    mp <> 0 -> 0 <= bm_in_ch bs -> 0 <= bm_out_ch bs ->
    (bm_in_ch bs = 0 \/ (2 <= bm_in_ch bs <= 40 /\ bm_in_ch bs mod 2 = 0)) ->
    (bm_out_ch bs = 0 \/ (2 <= bm_out_ch bs <= 40 /\ bm_out_ch bs mod 2 = 0)) ->
    evt rsegs Qw
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 (Z_to_bv 64 (bm_in_ch bs)) x2 x3 x4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x153b0) fc None m (seg_rom rsegs)).
  Proof.
    intros x0 x2 x3 x4 E Li Lo Hi Ho.
    assert (U : bm_uw mp bs = Z.max (bm_in_ch bs) 2).
    { unfold bm_uw, bm_wok. destruct Hi as [Hi|Hi]; destruct Ho as [Ho|Ho]; decide_tests; reflexivity. }
    pose proof (bm_in_ch_range bs) as Ri.
    step. step. rewrite (rc_ltu 2 (bm_in_ch bs)) by lia.
    destruct (Z.ltb_spec 2 (bm_in_ch bs)) as [G|G]; cbv iota.
    - step. step. apply evt_done. unfold Qw. rewrite U, Z.max_l by lia.
      do 4 eexists. reflexivity.
    - step. step. step. apply evt_done. unfold Qw. rewrite U, Z.max_r by lia.
      do 4 eexists. reflexivity.
  Qed.

  Lemma w_out : forall x0 x3 x4,
    mp <> 0 -> 0 <= bm_in_ch bs -> 0 <= bm_out_ch bs ->
    (bm_in_ch bs = 0 \/ (2 <= bm_in_ch bs <= 40 /\ bm_in_ch bs mod 2 = 0)) ->
    evt rsegs Qw
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 (Z_to_bv 64 (bm_in_ch bs)) (Z_to_bv 64 (bm_out_ch bs)) x3 x4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15394) fc None m (seg_rom rsegs)).
  Proof.
    intros x0 x3 x4 E Li Lo Hi. pose proof (bm_out_ch_range bs) as Ro.
    step. rewrite (rc_eqb (bm_out_ch bs) 0) by lia.
    destruct (Z.eqb_spec (bm_out_ch bs) 0) as [Zo|Zo]; cbv iota.
    - apply w_max; [exact E | exact Li | exact Lo | exact Hi | left; exact Zo].
    - step. step. step. rewrite (rc_addiw (bm_out_ch bs) (-41)) by lia.
      step. rewrite (rc_wok_ltu (bm_out_ch bs)) by lia.
      destruct (Z.leb_spec 2 (bm_out_ch bs)) as [G1|G1]; destruct (Z.leb_spec (bm_out_ch bs) 40) as [G2|G2];
        cbn [andb negb].
      + step. step. rewrite (rc_odd_eqb (bm_out_ch bs)) by lia.
        destruct (Z.eqb_spec (bm_out_ch bs mod 2) 0) as [Ev|Od]; cbn [negb].
        * apply w_max; [exact E | exact Li | exact Lo | exact Hi | right; lia].
        * step. destruct Hi as [Hi|Hi]; uw_zero mp bs.
      + step. destruct Hi as [Hi|Hi]; uw_zero mp bs.
      + step. destruct Hi as [Hi|Hi]; uw_zero mp bs.
      + step. destruct Hi as [Hi|Hi]; uw_zero mp bs.
  Qed.
End W.

Theorem reac_box_model_upstream_width_holds : reac_box_model_upstream_width_contract.
Proof.
  unfold reac_box_model_upstream_width_contract, REAC_BOX_MODEL_UPSTREAM_WIDTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mp bs
    Ha0 HM.
  pose proof (rc_word_range a0 mp Ha0) as Hr. apply rc_word in Ha0. subst a0.
  destruct (Z.eq_dec mp 0) as [E|E].
  - subst mp. step. if_true. step. apply evt_done. do 4 eexists. reflexivity.
  - destruct (HM E) as (H24 & Hlen & HB). clear HM.
    destruct (rc_rd4_opaque rsegs m (mp + 16) bs 0 HB ltac:(lia)) as (L1 & EL1 & RD1).
    destruct (rc_rd4_opaque rsegs m (mp + 16) bs 4 HB ltac:(lia)) as (L2 & EL2 & RD2).
    replace (mp + 16 + Z.of_nat 0) with (mp + 16) in RD1 by lia.
    replace (mp + 16 + Z.of_nat 4) with (mp + 20) in RD2 by lia.
    pose proof (bm_in_ch_range bs) as Ri. pose proof (bm_out_ch_range bs) as Ro.
    step. rewrite (rc_eqb mp 0) by lia. destruct (Z.eqb_spec mp 0); [lia|]. cbv iota.
    step. rewrite (rc_lw_in bs L1 EL1).
    step. rewrite (rc_lts0 (bm_in_ch bs)) by lia.
    destruct (Z.ltb_spec (bm_in_ch bs) 0) as [Ni|Ni]; cbv iota.
    + step. step. uw_zero mp bs.
    + step. rewrite (rc_lw_out bs L2 EL2).
      step. rewrite (rc_lts0 (bm_out_ch bs)) by lia.
      destruct (Z.ltb_spec (bm_out_ch bs) 0) as [No|No]; cbv iota.
      * step. step. uw_zero mp bs.
      * step. rewrite (rc_eqb (bm_in_ch bs) 0) by lia.
        destruct (Z.eqb_spec (bm_in_ch bs) 0) as [Zi|Zi]; cbv iota.
        -- apply w_out; [exact E | lia | lia | left; exact Zi].
        -- step. step. step. rewrite (rc_addiw (bm_in_ch bs) (-41)) by lia.
           step. rewrite (rc_wok_ltu (bm_in_ch bs)) by lia.
           destruct (Z.leb_spec 2 (bm_in_ch bs)) as [G1|G1]; destruct (Z.leb_spec (bm_in_ch bs) 40) as [G2|G2];
             cbn [andb negb].
           ++ step. step. rewrite (rc_odd_eqb (bm_in_ch bs)) by lia.
              destruct (Z.eqb_spec (bm_in_ch bs mod 2) 0) as [Ev|Od]; cbn [negb].
              ** apply w_out; [exact E | lia | lia | right; lia].
              ** step. uw_zero mp bs.
           ++ step. uw_zero mp bs.
           ++ step. uw_zero mp bs.
           ++ step. uw_zero mp bs.
Qed.
