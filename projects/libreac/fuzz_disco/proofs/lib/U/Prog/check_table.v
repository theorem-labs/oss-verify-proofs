From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table bcmp_c check_table_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_table_holds : bcmp_contract -> check_table_contract.
Proof.
  intros BC. unfold check_table_contract, CHECK_TABLE, CHECK_TABLE_K. unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t T -> Ht8 HT LT T1 T2 T3 MI ST LO DT.
  unfold tbl_T1 in T1. unfold off_window in DT.
  pose proof (bytes_at_bound rsegs m t T HT) as TB. rewrite LT in TB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 80%nat ST.
  do 11 step.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into mF end.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  lazymatch goal with H : rw_cells _ mF _ ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  do 3 step.
  rewrite land7_lit by lia. if_false.
  pose proof (rd_sub _ t T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  set (n := n_of T) in *.
  step. step.
  rewrite ltu_lit by lia. replace (8 <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  rewrite eqb_lit by lia.
  assert (EPI : forall (m2 : word -> option byte) (ra' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                        x21 x22 x23 x24 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m2 ->
    wmono rsegs mI m2 -> mem_inv rsegs m2 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
                          x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14678) fc None m2 (seg_rom rsegs))).
  { intros m2 ra' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2.
    unfold FRC in FR2.
    do 10 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|exact ST2]. }
  assert (OUTER : forall k i (m2 : word -> option byte) (ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x24
                          x28 x29 x30 x31 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m2 ->
    wmono rsegs mI m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 t T ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 t) x9 x10 x11 x12 x13
                          x14 x15 x16 x17 (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 (2^64 - 1 - t))
                          (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2) (Z_to_bv 64 7) x24 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14618) fc None m2 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m2 ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 Hk Hi FR2 ST2 MU2 WM2 MI2 HT2;
      [lia|].
    do 4 step.
    rewrite mul48_lit by lia.
    rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    pose proof (rd_sub _ t T (48 * i + 8) 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as RR.
    step.
    rewrite lw_val by (apply length_sub; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 8) 4))) with (role_of_e T i).
    assert (RL : role_of_e T i = 0 \/ role_of_e T i = 1 \/ role_of_e T i = 2) by (apply T2; lia).
    step.
    rewrite ltu_lit by lia. replace (2 <? role_of_e T i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    do 3 step.
    rewrite ltu_lit by lia.
    assert (AFTER : forall (m3 : word -> option byte) (ra'' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y24
                            y28 y29 y30 y31 : word),
      rw_cells rsegs m3 (bv_unsigned sp + -80) FRC ->
      stk rsegs m3 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m3 ->
      wmono rsegs mI m3 -> mem_inv rsegs m3 -> bytes_at rsegs m3 t T ->
      evt rsegs QQ (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y5 y6 y7 (Z_to_bv 64 t) y9 y10 y11 y12 y13
                            y14 y15 y16 y17 (Z_to_bv 64 n) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (2^64 - 1 - t))
                            (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2) (Z_to_bv 64 7) y24 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x14670) fc None m3 (seg_rom rsegs))).
    { intros m3 ra'' y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 FR3 ST3 MU3 WM3 MI3 HT3.
      do 2 step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (i + 1) n) as [E1|E1]; cbn [negb].
      - apply EPI; assumption.
      - replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
        apply (IH (i + 1)); try assumption; lia. }
    destruct (Z.ltb_spec (i + 1) n) as [L1|L1]; cbn [negb].
    - assert (INNER : forall k' j (m3 : word -> option byte) (ra'' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17
                              y28 y29 y30 y31 : word),
        Z.of_nat k' = n - j -> i + 1 <= j < n ->
        rw_cells rsegs m3 (bv_unsigned sp + -80) FRC ->
        stk rsegs m3 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m3 ->
        wmono rsegs mI m3 -> mem_inv rsegs m3 -> bytes_at rsegs m3 t T ->
        evt rsegs QQ (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y5 y6 y7 (Z_to_bv 64 t)
                              (Z_to_bv 64 (t + 48 * i)) y10 y11 y12 y13 y14 y15 y16 y17
                              (Z_to_bv 64 n) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (2^64 - 1 - t))
                              (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2) (Z_to_bv 64 7) (Z_to_bv 64 j)
                              s9 s10 s11 y28 y29 y30 y31)
                         F (Z_to_bv 64 0x14640) fc None m3 (seg_rom rsegs))).
      { induction k' as [|k' IH'];
          intros j m3 ra'' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Hk' Hj FR3 ST3 MU3 WM3 MI3 HT3;
          [lia|].
        step.
        rewrite ltu_lit by lia. replace (7 <? j) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
        do 4 step.
        rewrite mul48_lit by lia.
        rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * j) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
        do 4 step.
        destruct (memcmp6 (mac_of T i) (mac_of T j) ltac:(unfold mac_of; apply length_sub; lia)
                    ltac:(unfold mac_of; apply length_sub; lia)) as (v & Hv & Veq & Vr).
        eapply evt_cut.
        { eapply BC with (ls := mac_of T i) (rs := mac_of T j) (v := v).
          - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact HT3 | lia | rewrite LT; lia].
          - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact HT3 | lia | rewrite LT; lia].
          - exact Hv.
          - exact MI3. }
        post_call rsegs m3.
        assert (V0 : v <> 0) by (intro E; apply Veq in E; revert E; apply T3; lia).
        step.
        rewrite eqb_small by exact Vr. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact V0). cbv iota.
        do 2 step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (j + 1) n) as [Z0|Z0]; cbn [negb].
        - apply AFTER; assumption.
        - apply (IH' (j + 1)); try assumption; lia. }
      apply (INNER (Z.to_nat (n - (i + 1))) (i + 1)); try assumption; lia.
    - apply AFTER; assumption. }
  destruct (Z.eqb_spec n 0) as [N0|N0].
  - apply EPI; assumption.
  - do 5 step.
    rewrite not_lit by lia.
    replace (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)) by (f_equal; lia).
    apply (OUTER (Z.to_nat n) 0); try assumption; lia.
Qed.
