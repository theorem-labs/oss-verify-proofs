From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import put_blocks.
Import ListNotations.
Open Scope Z_scope.

Definition PJ_WRITE : Z := 0x14d1c.
Definition PJW_FRAME : Z := 48.
Definition WRITE_VALUE : Z := 0x14d8c.
Definition FUZZ_FREE : Z := 0x14378.
Definition PJW_WV_RET : Z := 0x14d50.
Definition PJW_PUT_RET : Z := 0x14d68.
Definition PJW_FREE_RET : Z := 0x14d78.
Definition STR_NL : Z := 0x1036a.

Lemma rw_cells_app : forall m A cs1 cs2 B, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A cs1 cs2 B [[Hwf Hb] Hw] EB. subst B.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  split; (split; [split; assumption |]).
  - apply (wr_at_shrink _ _ _ _ Hw). lia.
  - apply (wr_at_sub _ _ _ _ _ Hw); lia.
Qed.

Lemma rw_cells_zero_rec : forall m A,
  rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  pj_rec m A 0 0 0 0 (le4 (Z_to_bv 64 0)).
Proof.
  intros m A [[_ Hb] Hw]. unfold pj_rec. split; [split|].
  - exact (conj I (conj I (conj I (conj I (conj (length_le4 _) I))))).
  - eapply bytes_at_ext; [exact Hb|]. vm_compute. reflexivity.
  - exact Hw.
Qed.

Definition pjw_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (m : word -> option byte) (r : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs) /\
    stk rsegs m lo (bv_unsigned sp).

Theorem pjw_to_write_value :
  forall (ra sp gp tp t0 t1 t2 s0 s1 v pretty a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + PJW_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR (Z_to_bv 64 PJW_WV_RET) (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1
                       (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) v pretty (Z_to_bv 64 0) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 WRITE_VALUE) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - PJW_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp - PJW_FRAME) /\
         pj_rec m' (bv_unsigned sp - PJW_FRAME) 0 0 0 0 (le4 (Z_to_bv 64 0)) /\
         rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v pretty a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_WRITE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 v pretty a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST LO.
  unfold PJ_WRITE, PJW_FRAME, PJW_WV_RET, WRITE_VALUE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 48%nat ST.
  do 13 zstep.
  destruct (rw_cells_app _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 s0; C8 ra]
              (bv_unsigned sp - 16) FR ltac:(cbn; lia)) as [R1 R2].
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [|exact R2].
  apply rw_cells_zero_rec. exact R1.
Qed.

Theorem pjw_to_put_nl :
  forall (ra1 sp gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned pretty <> 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 PJW_PUT_RET) (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2
                                pretty s1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) (Z_to_bv 64 STR_NL) (Z_to_bv 64 1)
                                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJW_WV_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 sp gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HP.
  unfold PJW_FRAME, PJW_PUT_RET, PJW_WV_RET, STR_NL, PUT in *.
  zstep. if_cases BR; zify_cond BR; [exfalso; lia | clear BR].
  do 5 zstep.
  apply evt_done. reflexivity.
Qed.

Theorem pjw_skip_nl :
  forall (ra1 sp gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned pretty = 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5
                                a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PJW_PUT_RET) fc None m (seg_rom rsegs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJW_WV_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 sp gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HP.
  unfold PJW_FRAME, PJW_PUT_RET, PJW_WV_RET in *.
  zstep. if_cases BR; zify_cond BR; [clear BR | exfalso; lia].
  apply evt_done. reflexivity.
Qed.

Section PjwEpilogue.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo b l c f : Z) (pad : list byte) (m : word -> option byte).
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp - 48).
  Hypothesis LO : lo + 48 <= bv_unsigned sp.
  Hypothesis REC : pj_rec m (bv_unsigned sp - 48) b l c f pad.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp - 16) [C8 s0; C8 ra].
  Lemma pjw_epilogue : forall ra1 t0 t1 t2 g8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt rsegs (pjw_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m a0)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 g8 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14d7c) fc None m (seg_rom rsegs)).
  Proof using ST LO REC FR.
    intros.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    unfold pj_rec in REC.
    pose proof (stk_release _ _ _ _ _ ST REC ltac:(lia)) as ST1.
    replace (bv_unsigned sp - 48 + Z.of_nat (cells_size _)) with (bv_unsigned sp - 16) in ST1 by (cbn; lia).
    pose proof (stk_release _ _ _ _ _ ST1 FR ltac:(lia)) as ST2.
    replace (bv_unsigned sp - 16 + Z.of_nat (cells_size _)) with (bv_unsigned sp) in ST2 by (cbn; lia).
    replace (bv_unsigned sp - 16) with (bv_unsigned sp - 48 + 32) in FR by lia.
    do 3 zstep.
    replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
    rewrite Z_to_bv_bv_unsigned.
    zstep.
    apply evt_done. do 14 eexists. split; [reflexivity | exact ST2].
  Qed.
End PjwEpilogue.

Theorem pjw_ret_text :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo b l c : Z) (pad : list byte)
         (ra1 t0 t1 t2 pretty a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk rsegs m lo (bv_unsigned sp - PJW_FRAME) -> lo + PJW_FRAME <= bv_unsigned sp ->
    pj_rec m (bv_unsigned sp - PJW_FRAME) b l c 0 pad ->
    rw_cells rsegs m (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
    evt rsegs (pjw_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 b))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJW_PUT_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo b l c pad
    ra1 t0 t1 t2 pretty a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST LO REC FR.
  unfold PJW_FRAME, PJW_PUT_RET in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof REC as RC. unfold pj_rec in RC.
  zstep. zstep.
  zstep.
  if_true.
  eapply pjw_epilogue; eassumption.
Qed.

Theorem pjw_to_free :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo b l c f : Z) (pad : list byte)
         (ra1 t0 t1 t2 pretty a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    lo + PJW_FRAME <= bv_unsigned sp ->
    pj_rec m (bv_unsigned sp - PJW_FRAME) b l c f pad -> 0 < f < 2^32 ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 PJW_FREE_RET) (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1
                       (Z_to_bv 64 b) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FUZZ_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 pretty s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJW_PUT_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo b l c f pad
    ra1 t0 t1 t2 pretty a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LO REC HF.
  unfold PJW_FRAME, PJW_PUT_RET, PJW_FREE_RET, FUZZ_FREE in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  unfold pj_rec in REC.
  zstep. zstep.
  zstep.
  if_false_by (proj1 (negb_true_iff _) (sx32_nz f HF)).
  zstep.
  apply evt_done. eexists. reflexivity.
Qed.

Theorem pjw_ret_failed :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo b l c f : Z) (pad : list byte)
         (ra1 t0 t1 t2 g8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk rsegs m lo (bv_unsigned sp - PJW_FRAME) -> lo + PJW_FRAME <= bv_unsigned sp ->
    pj_rec m (bv_unsigned sp - PJW_FRAME) b l c f pad ->
    rw_cells rsegs m (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
    evt rsegs (pjw_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 0))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PJW_FRAME)) gp tp t0 t1 t2 g8 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJW_FREE_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo b l c f pad
    ra1 t0 t1 t2 g8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST LO REC FR.
  unfold PJW_FRAME, PJW_FREE_RET in *.
  zstep.
  eapply pjw_epilogue; eassumption.
Qed.
