From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg range_free_c lowest_free_c.
Import ListNotations.
Open Scope Z_scope.

Theorem lowest_free_holds : range_free_contract -> lowest_free_contract.
Proof.
  intros RF. unfold lowest_free_contract, LOWEST_FREE, LOWEST_FREE_FRAME. unfold RANGE_FREE in RF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t nch fabric bs -> -> -> Hn Hf HB HL B1 B2 B3 ST LO DJ.
  pose proof (bytes_at_bound rsegs m t bs HB) as TB. rewrite HL in TB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 64%nat ST.
  do 10 step.
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) => set (QQ := Q); rename mm into m1 end.
  assert (EPI : forall z (ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    lowest_free_res bs nch fabric z ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 z) x9
                          x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13748) fc None m1 (seg_rom rsegs))).
  { intros z ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 RES.
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. exists z. split; [reflexivity|exact RES]. }
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec fabric nch) as [Lt|Ge].
  - apply EPI. left. split; [reflexivity|]. intros b Hb. lia.
  - do 6 step.
    rewrite swrap_sub by lia. rewrite swrap_addi by lia.
    assert (LOOP : forall k b (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      Z.of_nat k = fabric - nch + 1 - b -> 0 <= b <= fabric - nch ->
      (forall b', 0 <= b' < b -> ~ range_free_ok bs b' nch fabric) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (-1))
                            (Z_to_bv 64 fabric) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nch) (Z_to_bv 64 t)
                            (Z_to_bv 64 b) (Z_to_bv 64 (fabric - nch + 1)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13720) fc None m1 (seg_rom rsegs))).
    { induction k as [|k IH]; intros b ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hb P; [lia|].
      do 5 step.
      eapply evt_cut.
      { eapply RF; try reflexivity; try eassumption; lia. }
      intros ms' Hp.
      destruct Hp as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E & R).
      subst ms'.
      replace (ret_pc (Z_to_bv 64 0x13734)) with (Z_to_bv 64 0x13734) by (apply bv_eq; vm_compute; reflexivity).
      destruct R as [[-> OK]|[-> NOK]].
      - step. if_true. step.
        apply EPI. right. split; [lia|]. split; [exact OK|exact P].
      - step. if_false. step.
        rewrite swrap_addi by lia.
        step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (fabric - nch + 1) (b + 1)) as [Eq|Ne].
        + cbn [negb]. step. apply EPI. left. split; [reflexivity|]. intros b' Hb'.
          destruct (Z.eq_dec b' b) as [->|NE]; [exact NOK|]. apply P. lia.
        + cbn [negb]. apply (IH (b + 1)); try lia.
          intros b' Hb'. destruct (Z.eq_dec b' b) as [->|NE]; [exact NOK|]. apply P. lia. }
    apply (LOOP (Z.to_nat (fabric - nch + 1)) 0); try lia.
Qed.
