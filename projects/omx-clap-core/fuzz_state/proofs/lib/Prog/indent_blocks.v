From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import put_blocks.
Import ListNotations.
Open Scope Z_scope.

Definition INDENT : Z := 0x15978.
Definition IND_FRAME : Z := 32.
Definition IND_NL_RET : Z := 0x159ac.
Definition IND_SP_RET : Z := 0x159c8.
Definition STR_NL : Z := 0x1036a.
Definition STR_SP2 : Z := 0x10375.

Lemma swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Definition ind_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs) /\
    stk rsegs m lo (bv_unsigned sp).

Theorem ind_nopretty :
  forall (ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned pretty = 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 INDENT) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HP.
  unfold INDENT.
  zstep. if_cases BR; zify_cond BR; [clear BR | exfalso; lia].
  zstep.
  apply evt_done. reflexivity.
Qed.

Theorem ind_to_put_nl :
  forall (ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned pretty <> 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + IND_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR (Z_to_bv 64 IND_NL_RET) (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2 dp o
                       o (Z_to_bv 64 STR_NL) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 PUT) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - IND_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp - IND_FRAME) /\
         rw_cells rsegs m' (bv_unsigned sp - IND_FRAME) [C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 INDENT) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 o pretty dp a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HP ST LO.
  unfold INDENT, IND_FRAME, IND_NL_RET, STR_NL, PUT in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  zstep. if_cases BR; zify_cond BR; [exfalso; lia | clear BR].
  carve_frame 32%nat ST.
  do 12 zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact FR].
Qed.

Section IndEpilogue.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte).
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp - 32).
  Hypothesis LO : lo + 32 <= bv_unsigned sp.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra].
  Lemma ind_epilogue : forall ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6,
    evt rsegs (ind_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
               g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x159d0) fc None m (seg_rom rsegs)).
  Proof using ST LO FR.
    intros.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    do 5 zstep.
    replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia.
    rewrite Z_to_bv_bv_unsigned.
    pose proof FR as FR'.
    release_frame FR' ST (bv_unsigned sp).
    zstep.
    apply evt_done. do 15 eexists. split; [reflexivity | exact ST].
  Qed.
End IndEpilogue.

Theorem ind_after_nl_done :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo d : Z)
         (ra1 t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6 : word),
    -2^31 <= d <= 0 ->
    stk rsegs m lo (bv_unsigned sp - IND_FRAME) -> lo + IND_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - IND_FRAME) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs (ind_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 d) g9 a0 a1 a2 a3 a4 a5 a6 a7
               g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IND_NL_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo d
    ra1 t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6 HD ST LO FR.
  unfold IND_FRAME, IND_NL_RET in *.
  zstep.
  if_cases BR; zify_cond BR; [ | exfalso; Z.div_mod_to_equations; lia].
  eapply ind_epilogue; eassumption.
Qed.

Theorem ind_after_nl_put :
  forall (ra1 sp gp tp t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d : Z),
    0 < d < 2^31 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 IND_SP_RET) (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2
                                (Z_to_bv 64 d) g9 g9 (Z_to_bv 64 STR_SP2) (Z_to_bv 64 2) a3 a4 a5 a6 a7
                                (Z_to_bv 64 STR_SP2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 d) g9 a0 a1 a2 a3 a4 a5 a6 a7
               g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IND_NL_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 sp gp tp t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d HD.
  unfold IND_FRAME, IND_NL_RET, IND_SP_RET, STR_SP2, PUT in *.
  zstep.
  if_cases BR; zify_cond BR; [exfalso; Z.div_mod_to_equations; lia |].
  do 6 zstep.
  apply evt_done. reflexivity.
Qed.

Theorem ind_loop_put :
  forall (ra1 sp gp tp t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d : Z),
    2 <= d < 2^31 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 IND_SP_RET) (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2
                                (Z_to_bv 64 (d - 1)) g9 g9 g18 (Z_to_bv 64 2) a3 a4 a5 a6 a7
                                g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 d) g9 a0 a1 a2 a3 a4 a5 a6 a7
               g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IND_SP_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 sp gp tp t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d HD.
  unfold IND_FRAME, IND_SP_RET, PUT in *.
  zstep. rewrite swrap32 by lia.
  zstep. if_cases BR; zify_cond BR; [clear BR | exfalso; lia].
  do 4 zstep.
  apply evt_done. reflexivity.
Qed.

Theorem ind_loop_done :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo : Z)
         (ra1 t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6 : word),
    stk rsegs m lo (bv_unsigned sp - IND_FRAME) -> lo + IND_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - IND_FRAME) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs (ind_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - IND_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 1) g9 a0 a1 a2 a3 a4 a5 a6 a7
               g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IND_SP_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo
    ra1 t0 t1 t2 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6 ST LO FR.
  unfold IND_FRAME, IND_SP_RET in *.
  zstep.
  zstep. if_cases BR; zify_cond BR; [exfalso; lia | clear BR].
  eapply ind_epilogue; eassumption.
Qed.
