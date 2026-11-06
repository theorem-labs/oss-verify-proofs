From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table find_entry_c role_of_c.
Import ListNotations.
Open Scope Z_scope.

Theorem role_of_holds : find_entry_contract -> role_of_contract.
Proof.
  intros FE. unfold role_of_contract, ROLE_OF, ROLE_OF_K. unfold find_entry_contract, FIND_ENTRY, FIND_ENTRY_K in FE.
  unfold FIND_ENTRY_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t p T P -> -> Ht0 Ht8 HT LT HP LP T1 T2 MI ST LO DT DP.
  unfold off_window in DT, DP.
  pose proof (bytes_at_bound rsegs m t T HT) as TB. rewrite LT in TB.
  pose proof (bytes_at_bound rsegs m p P HP) as PB. rewrite LP in PB.
  pose proof (munch_refl [(bv_unsigned sp - (16 + 80), bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  do 4 step.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into mF end.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  step.
  eapply evt_cut.
  { eapply FE with (lo := lo) (t := t) (p := p) (T := T) (P := P); try reflexivity; try assumption;
      unfold off_window; rewrite ?SPU; first [assumption | lia]. }
  intros ms' PO. rewrite SPU in PO. revert ms' PO.
  post_call rsegs mF.
  match goal with H : find_res T P ?r |- _ => rename r into ri; rename H into FRES end.
  assert (RR : -1 <= ri < n_of T) by (unfold tbl_T1 in T1; destruct FRES as [[-> _]|(? & _)]; lia).
  unfold tbl_T1 in T1.
  step.
  rewrite lts_lit by lia.
  lazymatch goal with H : rw_cells _ _ _ _ |- _ => rename H into FR end.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST end.
  destruct (Z.ltb_spec ri 0) as [Rn|Rn].
  - step. do 2 step.
    release_frame FR ST (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. exists (-1). split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [|left; reflexivity].
    exists ri. split; [exact FRES|]. replace (ri <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - do 2 step.
    rewrite land7_lit by lia. if_false.
    do 2 step.
    rewrite ltu_lit by lia. replace (ri <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    do 5 step.
    rewrite mul48_lit by lia. rewrite not_lit by lia.
    rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * ri) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    do 4 step.
    rewrite mul48_lit by lia.
    pose proof (rd_sub _ t T (48 * ri + 8) 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RD.
    step.
    rewrite lw_val by (apply length_sub; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * ri + 8) 4))) with (role_of_e T ri).
    step. do 2 step.
    release_frame FR ST (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. exists (role_of_e T ri). split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split.
    + exists ri. split; [exact FRES|]. replace (ri <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + right. apply T2. lia.
Qed.
