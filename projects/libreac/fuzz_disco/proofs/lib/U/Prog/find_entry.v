From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table bcmp_c find_entry_c.
Import ListNotations.
Open Scope Z_scope.

Theorem find_entry_holds : bcmp_contract -> find_entry_contract.
Proof.
  intros BC. unfold find_entry_contract, FIND_ENTRY, FIND_ENTRY_K. unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t p T P -> -> Ht0 Ht8 HT LT HP LP T1 MI ST LO DT DP.
  unfold tbl_T1 in T1. unfold off_window in DT, DP.
  pose proof (bytes_at_bound rsegs m t T HT) as TB. rewrite LT in TB.
  pose proof (bytes_at_bound rsegs m p P HP) as PB. rewrite LP in PB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 80%nat ST.
  do 10 step.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into mF end.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  lazymatch goal with H : rw_cells _ mF _ ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  do 3 step.
  rewrite land7_lit by lia. if_false.
  assert (EPI : forall (m2 : word -> option byte) r (ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                        x21 x22 x23 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m2 ->
    wmono rsegs mI m2 -> mem_inv rsegs m2 -> find_res T P r ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13
                          x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14de0) fc None m2 (seg_rom rsegs))).
  { intros m2 r ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2 RES.
    unfold FRC in FR2.
    do 10 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. exists r. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|exact RES]. }
  pose proof (rd_sub _ t T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  set (n := n_of T) in *.
  step. step.
  rewrite lts_lit by lia.
  assert (LOOP : forall k i (m2 : word -> option byte) (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    (forall j, 0 <= j < i -> mac_of T j <> P) ->
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] mI m2 ->
    wmono rsegs mI m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 t T -> bytes_at rsegs m2 p P ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 (-1))
                          (Z_to_bv 64 (t + 48 * i)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 i)
                          (Z_to_bv 64 (48 * i)) (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 384)
                          s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14da8) fc None m2 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m2 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi NP FR2 ST2 MU2 WM2 MI2 HT2 HP2; [lia|].
    step.
    rewrite eqb_lit by lia. replace (48 * i =? 384) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step.
    rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    do 4 step.
    destruct (memcmp6 (mac_of T i) P ltac:(unfold mac_of; apply length_sub; lia) LP) as (v & Hv & Veq & Vr).
    eapply evt_cut.
    { eapply BC with (ls := mac_of T i) (rs := P) (v := v).
      - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact HT2 | lia | rewrite LT; lia].
      - rewrite unsigned_lit by lia. exact HP2.
      - exact Hv.
      - exact MI2. }
    post_call rsegs m2.
    step.
    rewrite eqb_small by exact Vr.
    destruct (Z.eqb_spec v 0) as [V0|V0].
    - step.
      apply EPI; try assumption. right. split; [lia|]. split; [apply Veq; exact V0|exact NP].
    - assert (NE : mac_of T i <> P) by (intro E; apply V0; apply Veq; exact E).
      step.
      rewrite addiw_small by lia.
      do 4 step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (n - i + -1) 0) as [Z0|Z0]; cbn [negb].
      + step.
        apply EPI; try assumption. left. split; [reflexivity|].
        intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia.
      + replace (t + 48 * i + 48) with (t + 48 * (i + 1)) by lia.
        replace (48 * i + 48) with (48 * (i + 1)) by lia.
        replace (n - i + -1) with (n - (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; try lia.
        intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia. }
  destruct (Z.ltb_spec 0 n) as [Hn|Hn]; cbn [negb].
  - do 8 step.
    rewrite not_lit by lia. rewrite sgtz_and_lit by lia.
    replace (Z_to_bv 64 t) with (Z_to_bv 64 (t + 48 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (48 * 0)) at 1 by (f_equal; lia).
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
    apply (LOOP (Z.to_nat n) 0); try assumption; try lia.
  - apply EPI; try assumption. left. split; [reflexivity|]. intros j Hj. lia.
Qed.
