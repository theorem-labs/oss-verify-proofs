From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import memset_c memset_ro_c memset_ro.
Import ListNotations.
Open Scope Z_scope.

Lemma run_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo mn : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  bv_unsigned a1 * bv_unsigned a0 = mn -> mn < 4096 ->
  evt rsegs
    (fun ms' => exists (a2' : word) (m1 : word -> option byte) (junk : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x1459c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 mn)
                     (Z_to_bv 64 mn) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x147c4) fc None m1 (seg_rom rsegs) /\
       rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1454c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo mn ST LO HP HMN.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. unfold inr64 in Ra0, Ra1.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 32%nat ST.
  do 5 step.
  assert (E1 : Z_to_bv 64 (bv_unsigned a1 * bv_unsigned a0) = Z_to_bv 64 mn) by (rewrite HP; reflexivity).
  if_cases K0.
  - do 3 step. rewrite !E1.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact FR|]. split; [exact MU | exact WM].
  - step.
    assert (K1 : bv_eqb (Z_to_bv 64 ((bv_unsigned a1 * bv_unsigned a0) ≫ 64)) (Z_to_bv 64 0) = true).
    { rewrite HP, Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
    step. rewrite K1; cbv iota. do 3 step. rewrite !E1.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact FR|]. split; [exact MU | exact WM].
Qed.

Lemma run_ret0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (rao s0o s1o : word),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 0)
                          a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1465c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk rao s0o s1o FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  do 6 step.
  apply evt_done. reflexivity.
Qed.

Lemma run_retp : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (rao s0o s1o : word),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o s0
                          a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14578) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk rao s0o s1o FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  do 6 step.
  apply evt_done. reflexivity.
Qed.

Lemma run_clear : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk blk : list byte) (rao s0o s1o : word) (mn : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  0 <= mn < 4096 ->
  rw_cells rsegs m (bv_unsigned s0) [CB (Z.to_nat mn) blk] ->
  RoAdapt.not_ro rsegs (bv_unsigned s0) mn ->
  MemNorm.ro_agree rsegs m ->
  evt rsegs (memset_post_ro rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               s0 (Z_to_bv 64 0) (Z_to_bv 64 mn) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mn) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk blk rao s0o s1o mn FR Hmn BLK NRO RO.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  assert (K1 : bv_eqb (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 mn) ≫ 12)) (Z_to_bv 64 0) = true).
  { rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
  do 2 step. rewrite K1; cbv iota.
  do 8 step.
  eapply memset_ro_holds.
  - rewrite unsigned_lit by lia. exact BLK.
  - rewrite unsigned_lit by lia. replace (Z.of_nat (cells_size _)) with mn by (cbn [cells_size csize]; lia). exact NRO.
  - exact RO.
Qed.

Lemma run_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (rao s0o s1o : word),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 0)
                          a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1459c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk rao s0o s1o FR.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by reflexivity; cbv iota | _ => idtac end.
  exact (run_ret0 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m junk rao s0o s1o FR).
Qed.

Lemma run_some : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rb : list byte),
  bv_eqb a0 (Z_to_bv 64 0) = false ->
  ro_cells rsegs m 0x4eae8 [CB 4 rb] ->
  evt rsegs
    (fun ms' => (exists a0r, ms' = MS (mkR ra sp gp tp t0 t1 t2 a0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x145b0) fc None m (seg_rom rsegs)) \/
                ms' = MS (mkR (Z_to_bv 64 0x1467c) sp gp tp t0 t1 t2 a0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15eb8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1459c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rb Hnz RB.
  step. rewrite Hnz; cbv iota.
  do 4 step.
  if_cases K1.
  - do 2 step. apply evt_done. right. reflexivity.
  - apply evt_done. left. eexists. reflexivity.
Qed.

Lemma run_azret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (rao s0o s1o : word),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs
    (fun ms' => (bv_eqb a0 (Z_to_bv 64 0) = false /\
                 ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o s0
                               a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc rao) fc None m (seg_rom rsegs)) \/
                ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x145b0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1467c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk rao s0o s1o FR.
  step.
  if_cases K0.
  - eapply evt_mono.
    + exact (run_retp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m junk rao s0o s1o FR).
    + intros ms' Hm. left. split; [apply negb_true_iff; exact K0 | exact Hm].
  - step. apply evt_done. right. reflexivity.
Qed.
