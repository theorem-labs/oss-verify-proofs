From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import fuzz_alloc_peak_c check_bounded_alloc_c
  check_reject_clean_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sb_rd_sp : forall m (sp w : word), bytes_at rsegs m (bv_unsigned sp) (le8 w) ->
  ov_read_bytes rsegs m sp 8 = Some (le8 w).
Proof.
  intros m sp w H.
  replace sp with (wa (bv_unsigned sp + 0)) by (unfold wa; rewrite Z.add_0_r; apply Z_to_bv_lit_self).
  rewrite (bytes_at_read rsegs m (bv_unsigned sp) (le8 w) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma sB_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nn : Z),
  s1 = Z_to_bv 64 nn -> 0 <= nn < 2 ^ 63 ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13374) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (nn + 1)) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16594) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1336c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nn E1 Hn.
  subst s1.
  do 2 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma sD_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nn lv pk : Z) (lenw : word),
  fuzz_alloc_peak_contract -> check_bounded_alloc_contract ->
  s1 = Z_to_bv 64 nn -> 0 <= nn < 2 ^ 64 -> s3 = Z_to_bv 64 lv -> 0 <= lv <= pk -> pk < 2 ^ 64 ->
  pk - lv <= b64_alloc_bound nn ->
  bytes_at rsegs m 0x33458 (le8 (Z_to_bv 64 pk)) ->
  bytes_at rsegs m (bv_unsigned sp) (le8 lenw) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR (Z_to_bv 64 0x133d4) sp gp tp t0' t1' t2' s0 s1 s0 a0 lenw a3' a4' a5' a6' a7'
                    a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x135ec) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    nn lv pk lenw FAP CBA E1 Hn E3 Hlv Hpk Hb PK LW.
  subst s1 s3.
  pose proof (sb_rd_sp m sp lenw LW) as RD.
  do 2 zstep.
  eapply evt_cut.
  { eapply FAP with (peak := Z_to_bv 64 pk). exact PK. }
  intros ms' POST. cbv beta in POST. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x133b8)) with (Z_to_bv 64 0x133b8) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  eapply evt_cut.
  { eapply CBA. rewrite !unsigned_lit by lia. exact Hb. }
  intros ms' (a1' & a2' & POST). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x133c4)) with (Z_to_bv 64 0x133c4) by (apply bv_eq; vm_compute; reflexivity).
  do 4 zstep.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Lemma sE0_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  check_reject_clean_contract ->
  s2 = Z_to_bv 64 0 ->
  bytes_at rsegs m (bv_unsigned sp) (le8 (Z_to_bv 64 (2 ^ 64 - 1))) ->
  bytes_at rsegs m 0x33450 (le8 s3) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x33450 + 8 <= bv_unsigned sp - 16 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x1340c) sp gp tp t0' t1' t2' s0 s1 s0 s2 (Z_to_bv 64 (2 ^ 64 - 1)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13d84) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo CRC E2 LW LV ST Hlo Hg.
  subst s2.
  pose proof (sb_rd_sp m sp _ LW) as RD.
  zstep. zstep. if_true.
  do 4 zstep.
  eapply evt_cut.
  { eapply CRC with (lo := lo) (live := s3).
    - exact ST.
    - unfold CHECK_REJECT_CLEAN_FRAME. lia.
    - exact LV.
    - left. change (0x33450 + 8 <= bv_unsigned sp - 16). lia.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & E & MU & WM & ST').
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x133fc)) with (Z_to_bv 64 0x133fc) by (apply bv_eq; vm_compute; reflexivity).
  apply (bytes_at_transport rsegs [(bv_unsigned sp - CHECK_REJECT_CLEAN_FRAME, bv_unsigned sp)] m m') in LW;
    [| exact MU | cbn [disjoint_from]; rewrite length_le8; unfold CHECK_REJECT_CLEAN_FRAME; lia].
  clear RD. pose proof (sb_rd_sp m' sp _ LW) as RD.
  do 4 zstep.
  apply evt_done. do 12 eexists. exists m'. split; [reflexivity|].
  split; [exact MU | exact WM].
Qed.

Lemma sE1_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bd : Z) (lenw : word),
  s2 = Z_to_bv 64 bd -> 0 < bd < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned sp) (le8 lenw) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR (Z_to_bv 64 0x133e8) sp gp tp t0' t1' t2' s0 s1 s0 s2 lenw a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x138ac) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bd lenw E2 Hbd LW.
  pose proof (sb_rd_sp m sp lenw LW) as RD.
  assert (B : bv_eqb s2 (Z_to_bv 64 0) = false).
  { subst s2. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  zstep. zstep. rewrite B; cbv iota.
  do 3 zstep.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Lemma sF_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lenw : word),
  bytes_at rsegs m (bv_unsigned sp) (le8 lenw) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR (Z_to_bv 64 0x1340c) sp gp tp t0' t1' t2' s0 s1 s0 s2 lenw a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13d84) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lenw LW.
  pose proof (sb_rd_sp m sp lenw LW) as RD.
  do 5 zstep.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Lemma sG_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13414) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1340c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma sH_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x1341c) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13414) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma sI_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x0 xs3 xs2 xs1 xs0 xra : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 x0; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1341c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m x0 xs3 xs2 xs1 xs0 xra FR.
  do 8 zstep.
  apply evt_done. reflexivity.
Qed.
