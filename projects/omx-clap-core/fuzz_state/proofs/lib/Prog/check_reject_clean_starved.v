From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import fuzz_alloc_live_c fuzz_alloc_fail_c check_reject_clean_c.
Import ListNotations.
Open Scope Z_scope.

Lemma crs_fail0 : forall c, bv_unsigned c < 2 ^ 63 -> fail_at_of c (Z_to_bv 64 0) = c.
Proof.
  intros c H. unfold fail_at_of. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply Z_to_bv_lit_self.
Qed.

Lemma crs_failm1 : forall c, 1 <= bv_unsigned c ->
  fail_at_of c (Z_to_bv 64 (-1)) = Z_to_bv 64 18446744073709551615.
Proof.
  intros c H. unfold fail_at_of. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma crs_seg1 : fuzz_alloc_live_contract -> fuzz_alloc_fail_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (live count : word),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x55000 <= lo ->
  bytes_at rsegs m G_LIVE (le8 live) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  bv_unsigned count < 2 ^ 63 ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13dcc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 live a2 a0
                    (Z_to_bv 64 (bv_unsigned sp + -48)) a2 a3 a4 a5 a6 a7 a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      bytes_at rsegs m' G_FAIL_AT (le8 count) /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d84) fc None m (seg_rom rsegs)).
Proof.
  intros FAL FAF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    live count ST LO HLO HL HC HF Hc.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m) as MU.
  unfold G_LIVE, G_COUNT, G_FAIL_AT in *.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  carve_frame 48%nat ST.
  do 10 zstep.
  eapply evt_cut; [eapply FAL; exact HL | intros ms' E; cbv beta in E; subst ms'].
  replace (ret_pc (Z_to_bv 64 0x13dac)) with (Z_to_bv 64 0x13dac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 5 zstep.
  eapply evt_cut; [eapply FAF; [exact HC | exact HF] | intros ms' POST].
  destruct POST as (a1' & m2 & E & BF & MUc & WMc). subst ms'.
  unfold G_FAIL_AT in MUc, BF.
  transport_after_call rsegs m1 m2 MUc WMc.
  rewrite (crs_fail0 count Hc) in *.
  replace (ret_pc (Z_to_bv 64 0x13dc0)) with (Z_to_bv 64 0x13dc0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 3 zstep.
  apply evt_done. exists m2. split; [reflexivity|].
  split; [exact FR|]. split; [exact BF|]. split; [exact MU | exact WM].
Qed.

Lemma crs_seg2a : fuzz_alloc_fail_contract -> check_reject_clean_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (count xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 18446744073709551615); C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x55000 <= lo ->
  bytes_at rsegs m G_LIVE (le8 s0) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  1 <= bv_unsigned count -> a0 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13de8) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13de8) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 18446744073709551615); C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] /\
      stk rsegs m' lo (bv_unsigned sp) /\
      bytes_at rsegs m' G_FAIL_AT (le8 (Z_to_bv 64 18446744073709551615)) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dcc) fc None m (seg_rom rsegs)).
Proof.
  intros FAF CRC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    count xra xs0 xs1 xs2 xs3 FR ST LO HLO HL HC HF Hc ->.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold G_LIVE, G_COUNT, G_FAIL_AT in *.
  do 3 zstep.
  eapply evt_cut; [eapply FAF; [exact HC | exact HF] | intros ms' POST].
  destruct POST as (a1' & m2 & E & BF & MUc & WMc). subst ms'.
  unfold G_FAIL_AT in MUc, BF.
  transport_after_call rsegs m m2 MUc WMc.
  rewrite (crs_failm1 count Hc) in *. clear MUc WMc.
  replace (ret_pc (Z_to_bv 64 0x13dd8)) with (Z_to_bv 64 0x13dd8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 4 zstep.
  eapply evt_cut.
  { eapply CRC; [exact ST | unfold CHECK_REJECT_CLEAN_FRAME; lia | exact HL | unfold G_LIVE, CHECK_REJECT_CLEAN_FRAME; lia |
      reflexivity | reflexivity | reflexivity]. }
  intros ms' POST.
  destruct POST as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & E & MUd & WMd & ST3).
  subst ms'. unfold CHECK_REJECT_CLEAN_FRAME in MUd.
  transport_after_call rsegs m2 m3 MUd WMd.
  replace (ret_pc (Z_to_bv 64 0x13de8)) with (Z_to_bv 64 0x13de8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  apply evt_done. do 15 eexists. exists m3. split; [reflexivity|].
  split; [exact FR|]. split; [exact ST3|]. split; [exact BF|]. split; [exact MU | exact WM].
Qed.

Lemma crs_seg2r :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 v; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  s2 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13de8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v xra xs0 xs1 xs2 xs3 FR ->.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs m _ _ FR) as RB. cbn [cells_size csize Nat.add] in RB.
  zstep. if_true.
  do 7 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma crs_seg2e : fuzz_alloc_fail_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (count : word),
  bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  bv_unsigned count < 2 ^ 63 -> bv_unsigned s2 <> 0 ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13e00) sp gp tp t0 t1 t2 s0 s1 s2 s1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14d10) fc None m' (seg_rom rsegs) /\
      bytes_at rsegs m' G_FAIL_AT (le8 count) /\
      munch [(G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13de8) fc None m (seg_rom rsegs)).
Proof.
  intros FAF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    count HC HF Hc Hs2.
  zstep. if_false.
  do 2 zstep.
  eapply evt_cut; [eapply FAF; [exact HC | exact HF] | intros ms' POST].
  destruct POST as (a1' & m2 & E & BF & MUc & WMc). subst ms'.
  rewrite (crs_fail0 count Hc) in *.
  replace (ret_pc (Z_to_bv 64 0x13df4)) with (Z_to_bv 64 0x13df4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 3 zstep.
  apply evt_done. exists m2. split; [reflexivity|].
  split; [exact BF|]. split; [exact MUc | exact WMc].
Qed.

Lemma crs_seg3 : fuzz_alloc_live_contract -> fuzz_alloc_fail_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (count v xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 v; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  bytes_at rsegs m G_LIVE (le8 s0) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  1 <= bv_unsigned count -> a0 = Z_to_bv 64 0 -> 0x55000 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists (a1' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 xs0 xs1 s0 a1' a2 a3 a4 a5 a6 a7
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      bytes_at rsegs m' G_FAIL_AT (le8 (Z_to_bv 64 18446744073709551615)) /\
      munch [(G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e00) fc None m (seg_rom rsegs)).
Proof.
  intros FAL FAF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    count v xra xs0 xs1 xs2 xs3 FR HL HC HF Hc -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs m _ _ FR) as RB. cbn [cells_size csize Nat.add] in RB.
  unfold G_LIVE, G_COUNT, G_FAIL_AT in *.
  do 3 zstep.
  eapply evt_cut; [eapply FAF; [exact HC | exact HF] | intros ms' POST].
  destruct POST as (a1' & m2 & E & BF & MUc & WMc). subst ms'.
  unfold G_FAIL_AT in MUc, BF.
  transport_after_call rsegs m m2 MUc WMc.
  rewrite (crs_failm1 count Hc) in *.
  replace (ret_pc (Z_to_bv 64 0x13e0c)) with (Z_to_bv 64 0x13e0c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  zstep. if_false.
  zstep.
  eapply evt_cut; [eapply FAL; exact HL | intros ms' E; cbv beta in E; subst ms'].
  replace (ret_pc (Z_to_bv 64 0x13e14)) with (Z_to_bv 64 0x13e14) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  zstep. if_false.
  do 7 zstep.
  apply evt_done. exists a1', m2. split; [reflexivity|].
  split; [exact BF|]. split; [exact MUc | exact WMc].
Qed.

Lemma crs_seg2_ret : fuzz_alloc_fail_contract -> check_reject_clean_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (count xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 18446744073709551615); C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x55000 <= lo ->
  bytes_at rsegs m G_LIVE (le8 s0) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  1 <= bv_unsigned count -> a0 = Z_to_bv 64 0 -> s2 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7'
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      bytes_at rsegs m' G_FAIL_AT (le8 (Z_to_bv 64 18446744073709551615)) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dcc) fc None m (seg_rom rsegs)).
Proof.
  intros FAF CRC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    count xra xs0 xs1 xs2 xs3 FR ST LO HLO HL HC HF Hc E0 E2.
  eapply evt_cut; [eapply (crs_seg2a FAF CRC); eassumption |].
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & FR' & _ & BF & MU & WM).
  eapply evt_mono; [eapply crs_seg2r; [exact FR' | exact E2] |].
  intros ms'' ->. exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, m'.
  split; [reflexivity|]. split; [exact BF|]. split; [exact MU | exact WM].
Qed.

Lemma crs_seg2_enc : fuzz_alloc_fail_contract -> check_reject_clean_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (count xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 18446744073709551615); C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x55000 <= lo ->
  bytes_at rsegs m G_LIVE (le8 s0) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_FAIL_AT 8 ->
  1 <= bv_unsigned count -> bv_unsigned count < 2 ^ 63 -> a0 = Z_to_bv 64 0 -> bv_unsigned s2 <> 0 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13e00) sp gp tp t0' t1' t2' s0 s1 s2 s1 a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14d10) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 18446744073709551615); C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] /\
      bytes_at rsegs m' G_FAIL_AT (le8 count) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp); (G_FAIL_AT, G_FAIL_AT + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dcc) fc None m (seg_rom rsegs)).
Proof.
  intros FAF CRC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    count xra xs0 xs1 xs2 xs3 FR ST LO HLO HL HC HF Hc1 Hc2 E0 E2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  eapply evt_cut; [eapply (crs_seg2a FAF CRC); eassumption |].
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m2 & -> & FR2 & _ & BF2 & MU & WM).
  assert (HC2 : bytes_at rsegs m2 G_COUNT (le8 count)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ HC MU). unfold G_COUNT, G_FAIL_AT. rewrite length_le8.
    cbn [disjoint_from]. lia. }
  pose proof (wr_at_transport rsegs m m2 _ _ HF WM) as HF2.
  eapply evt_mono; [eapply (crs_seg2e FAF); [exact HC2 | exact HF2 | exact Hc2 | exact E2] |].
  intros ms'' (m3 & -> & BF3 & MU3 & WM3).
  exists u0, u1, u2, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, m3. split; [reflexivity|].
  split.
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). unfold G_FAIL_AT. cbn [disjoint_from cells_size csize Nat.add].
    lia. }
  split; [exact BF3|].
  split; [|exact (wmono_trans rsegs m m2 m3 WM WM3)].
  apply (munch_trans _ m m2 m3 MU). eapply munch_weaken; [|exact MU3]. unfold sub_fp. cbn [outside]. tauto.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger KindBGlue HState HStateRoom WriterSpec
  check_as_written_c fuzz_malloc_c preset_base64_decode_c preset_base64_encode_c check_reject_clean_starved_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts HsKindB.
Local Open Scope Z_scope.

Lemma crs_fs_hi : forall a, 0x55000 <= a -> find_segment rsegs a 1 = None.
Proof. intros a Ha. apply (HsKindB.find_segment_above rsegs 0x55000 a 1 HsKindB.rsegs_top); lia. Qed.

Lemma crs_wr_hi : forall (m : word -> option byte) a, 0x55000 <= a < 2 ^ 64 ->
  (writable_at rsegs m a <-> mbyte rsegs m a <> None).
Proof.
  intros m a Ha.
  assert (F : find_segment rsegs (bv_unsigned (Z_to_bv 64 a)) 1 = None)
    by (rewrite MState.unsigned_lit by lia; apply crs_fs_hi; lia).
  unfold writable_at, mbyte. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - split; intros _; [discriminate|]. unfold wview. rewrite E. discriminate.
  - pose proof (seg_rom_unmapped rsegs _ F) as R0.
    change (YK11.seg_rom rsegs (Z_to_bv 64 a)) with (PropExec.seg_rom rsegs (Z_to_bv 64 a)). rewrite R0.
    unfold wview. rewrite E, F. tauto.
Qed.

Lemma crs_rw_keep : forall m m' A cs, 0x55000 <= A -> Step.rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> mbyte rsegs m' a = mbyte rsegs m a) ->
  Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs HA RW H. pose proof (Step.rw_cells_bound rsegs m A cs RW) as RB.
  apply (HsKindB.rw_cells_keep m m' A cs RW). intros a Ha. split; [exact (H a Ha)|].
  rewrite !crs_wr_hi by lia. rewrite (H a Ha). tauto.
Qed.

Lemma crs_window : forall sp K lo hi, (forall a, lo <= a < hi -> ~ in_window sp K a) -> lo < hi -> 0 < K ->
  hi <= sp - K \/ sp <= lo.
Proof.
  intros sp K lo hi H Hlh HK. destruct (Z_le_gt_dec hi (sp - K)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec sp lo) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max lo (sp - K))); [lia | unfold in_window; lia].
Qed.

Lemma crs_disj : forall a n lo hi, (forall x, a <= x < a + n -> ~ (lo <= x < hi)) -> lo < hi -> 0 < n ->
  a + n <= lo \/ hi <= a.
Proof.
  intros a n lo hi H Hlh Hn. destruct (Z_le_gt_dec (a + n) lo) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec hi a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a lo)); lia.
Qed.

Lemma crs_align : forall t n r x, 0 <= r < 8 -> (t + n + 1 + r) mod 8 = 0 -> t + n + 1 <= x < t + n + 1 + r ->
  G_FAIL <= x < G_FAIL + 8 -> G_FAIL <= t + n < G_FAIL + 8.
Proof.
  intros t n r x Hr Hm Hx Hg. unfold G_FAIL in *.
  pose proof (Z.div_mod (t + n + 1 + r) 8 ltac:(lia)) as D. rewrite Hm in D.
  set (q := (t + n + 1 + r) / 8) in D. lia.
Qed.

Lemma crs_six_len : forall six, (length (six_bytes six) <= length six)%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [six_bytes length]; try lia.
  specialize (IH r). lia.
Qed.

Lemma crs_dec_len : forall tb bs, b64_dec tb = Some bs -> (length bs <= length tb)%nat.
Proof.
  intros tb bs H. unfold b64_dec in H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (crs_six_len six). lia.
Qed.

Lemma crs_bv8 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma crs_map_zs : forall tb, map (Z_to_bv 8) (zs tb) = tb.
Proof.
  intros tb. unfold zs. rewrite map_map. rewrite <- (map_id tb) at 2. apply map_ext. exact crs_bv8.
Qed.

Lemma crs_zs_len : forall tb, length (zs tb) = length tb.
Proof. intros tb. unfold zs. apply length_map. Qed.

Lemma crs_zs_bytes : forall tb, bytes_ok (zs tb).
Proof.
  intros tb. unfold bytes_ok, zs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma crs_zs_nz : forall tb, ~ In (Z_to_bv 8 0) tb -> no_zero (zs tb).
Proof.
  intros tb H. unfold no_zero, zs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
  intros E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma crs_zs_nth : forall (bsd : list byte) k, Z_to_bv 8 (nth k (zs bsd) 0) = nth k bsd (Z_to_bv 8 0).
Proof.
  intros bsd k. unfold zs. change 0 with (bv_unsigned (Z_to_bv 8 0)) at 1. rewrite map_nth. apply crs_bv8.
Qed.

Lemma crs_lsum : forall Lam, Forall (fun ak => 0 <= snd ak) Lam -> 0 <= lsum Lam.
Proof. induction 1 as [|[a k] r Hk _ IH]; cbn [lsum snd] in *; lia. Qed.

Lemma crs_layout_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (H1 & H2 & H3 & H4) (K1 & K2 & K3 & K4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (K4 r ltac:(lia)). apply H4. exact Hr.
Qed.

Lemma crs_rp : forall regs (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  sp = getr regs 2 -> gp = getr regs 3 -> tp = getr regs 4 -> s0 = getr regs 8 -> s1 = getr regs 9 ->
  s2 = getr regs 18 -> s3 = getr regs 19 -> s4 = getr regs 20 -> s5 = getr regs 21 -> s6 = getr regs 22 ->
  s7 = getr regs 23 -> s8 = getr regs 24 -> s9 = getr regs 25 -> s10 = getr regs 26 -> s11 = getr regs 27 ->
  regs_preserved regs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof. intros. subst. kb_saved. Qed.

Definition crs_R1 (regs : bvmap 5 word) (live : word) : bvmap 5 word :=
  mkR (Z_to_bv 64 0x13dcc) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -48)) (getr regs 3) (getr regs 4)
    (getr regs 5) (getr regs 6) (getr regs 7) live (getr regs 12) (getr regs 10)
    (Z_to_bv 64 (bv_unsigned (getr regs 2) + -48)) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
    (getr regs 16) (getr regs 17) (getr regs 11) (getr regs 10) (getr regs 20) (getr regs 21) (getr regs 22)
    (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
    (getr regs 30) (getr regs 31).

Lemma crs_R1_saved : forall regs live k, k = 3 \/ k = 4 \/ 20 <= k <= 27 ->
  getr (crs_R1 regs live) (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).
Proof.
  intros regs live k Hk.
  assert (H : k = 3 \/ k = 4 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Lemma crs_R4_saved : forall regs (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : word) k,
  k = 3 \/ k = 4 \/ 20 <= k <= 27 ->
  getr (mkR (Z_to_bv 64 0x13e00) (getr regs 2) (getr regs 3) (getr regs 4) u0 u1 u2 (getr regs 8) (getr regs 9)
    (getr regs 18) (getr regs 9) u3 u4 u5 u6 u7 u8 (getr regs 18) (Z_to_bv 64 0) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) u9 u10 u11 u12)
    (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).
Proof.
  intros regs u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 k Hk.
  assert (H : k = 3 \/ k = 4 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma crs_own_mid : YL01.AllocExtra B MR -> ctx_owned B API ->
  forall L A m md L1 A1 m1 md1 a, MR L A m md -> MR L1 A1 m1 md1 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L1 A1 a.
Proof.
  intros AX CO L A m md L1 A1 m1 md1 a HM HM1 Hr Hn Ho.
  destruct Hr as [Hr | Hr].
  - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
  - destruct Ho as [Ho | Ho].
    + apply Hn. apply (CO L A m md a HM). exact (YL01.ax_img AX L1 A1 m1 md1 a HM1 Hr Ho).
    + apply Hn. right. exact Ho.
Qed.

Lemma crs_seq : forall K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2,
  kb_mid B API K sp L A mem md E1 L1 A1 mem1 md1 ->
  kb_mid B API K2 sp2 L1 A1 mem1 md1 E2 L2 A2 mem2 md2 ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp ->
  (length (st_regions A) <= length (st_regions A1))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2) -> In (p, n) (user_blocks A1)) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L2 A2 a ->
     ~ owned B L1 A1 a) ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     writable_at (ms_segs B) mem1 a -> writable_at (ms_segs B) mem2 a) ->
  kb_mid B API K sp L A mem md (fun a => E1 a \/ E2 a) L2 A2 mem2 md2.
Proof.
  intros K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) (M2 & W2 & B2 & Y2 & P2 & D2 & F2 & K2' & S2)
    H1 H2 H3 HLEN HUB HOWN HW.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split; [exact (crs_layout_trans A A1 L L1 L2 Y1 Y2 HLEN)|].
  split; [intros p n Hp Hp2; pose proof (HUB p n Hp Hp2) as Hp1; rewrite (P2 p n Hp1 Hp2); exact (P1 p n Hp Hp1)|].
  split; [destruct D1 as (vm1 & ->); destruct D2 as (vm2 & ->); exists vm2; reflexivity|].
  split.
  { intros a Ha Ho Ho2 Hs He.
    pose proof (HOWN a Ha Ho Ho2) as Ho1.
    destruct (F1 a Ha Ho Ho1 Hs ltac:(tauto)) as [E1a E1w].
    destruct (F2 a Ha Ho1 Ho2 ltac:(intros [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]) ltac:(tauto))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 Hi. pose proof (HUB p n Hp Hp2) as Hp1.
    rewrite <- (P1 p n Hp Hp1). rewrite (K2' p n i Hp1 Hp2 Hi). rewrite (P1 p n Hp Hp1). exact (K1 p n i Hp Hp1 Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  apply HW; [exact Ha | tauto | tauto | apply S1; left; exact Ha].
Qed.

Lemma crs_mid_E : forall K sp L A mem md (E E' : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' -> (forall a, ~ (sp - K <= a < sp) -> E a -> E' a) ->
  kb_mid B API K sp L A mem md E' L' A' mem' md'.
Proof.
  intros K sp L A mem md E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He'. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros He. apply He'. apply HE; [intros Hx; apply Hs; left; exact Hx | exact He].
Qed.

Lemma crs_out_own : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall L A mem md lo hi x, MR L A mem md -> alloc_ceiling <= lo -> 0 <= x < alloc_ceiling ->
  (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
  Frame.outside [(lo, hi); (G_FAIL, G_FAIL + 8)] x.
Proof.
  intros GF L A mem md lo hi x HM Hlo Hx Ho.
  assert (O : Frame.outside [(G_FAIL, G_FAIL + 8)] x).
  { apply (globals_avoid B API _ [(G_FAIL, G_FAIL + 8)] L A mem md GF HM); [|exact Hx | exact Ho].
    intros lo' hi' y Hin Hy. destruct Hin as [E|[]]. injection E as <- <-.
    exists G_FAIL, 8. split; [left; reflexivity | lia]. }
  cbn [Frame.outside] in *. split; [lia | exact O].
Qed.

Lemma crs_blk_notG : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall L A mem md p k x, MR L A mem md -> In (p, k) (blocks L A) -> p <= x < p + k ->
  ~ (G_FAIL <= x < G_FAIL + 8).
Proof.
  intros GF L A mem md p k x HM Hin Hx Hg.
  destruct (GF x ltac:(exists G_FAIL, 8; split; [left; reflexivity | lia])) as (_ & _ & _ & _ & H).
  destruct (H L A mem md HM) as [_ Hb]. exact (Hb p k Hin Hx).
Qed.

Lemma crs_ro_G : forall x, G_FAIL <= x < G_FAIL + 8 -> Mem.ro_addr rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold G_FAIL in Hx.
  assert (H : x = 143840 \/ x = 143841 \/ x = 143842 \/ x = 143843 \/ x = 143844 \/ x = 143845 \/ x = 143846 \/
              x = 143847) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma crs_ro_munch : forall m m' lo hi, ro_agree rsegs m -> Frame.munch [(lo, hi); (G_FAIL, G_FAIL + 8)] m m' ->
  0x55000 <= lo -> ro_agree rsegs m'.
Proof.
  intros m m' lo hi RA MU Hlo a Ha.
  pose proof (zr_word a) as R. unfold inr64 in R.
  assert (Ho : Frame.outside [(lo, hi); (G_FAIL, G_FAIL + 8)] (bv_unsigned a)).
  { cbn [Frame.outside]. split; [|split; [|exact I]].
    - intros H. unfold Mem.ro_addr in Ha. rewrite crs_fs_hi in Ha by lia. discriminate.
    - intros H. rewrite <- (Z_to_bv_bv_unsigned a) in Ha. rewrite (crs_ro_G _ H) in Ha. discriminate. }
  unfold Mem.mrd. rewrite (MU a Ho). exact (RA a Ha).
Qed.

Lemma crs_ledger_munch : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall L A mem md mem' lo hi Lam peak c f f', MR L A mem md -> ledger B L A mem Lam peak c f ->
  Frame.munch [(lo, hi); (G_FAIL, G_FAIL + 8)] mem mem' -> alloc_ceiling <= lo ->
  word_mem (ms_segs B) mem' G_FAIL f' -> 0 <= f' < 2 ^ 64 -> ledger B L A mem' Lam peak c f'.
Proof.
  intros GF L A mem md mem' lo hi Lam peak c f f' HM (AW & R1 & R2 & R3 & ND & FA) MU Hlo HW Hf.
  pose proof alloc_ceiling_val as Hac. destruct AW as (W1 & W2 & W3 & _).
  assert (K : forall a v, 0 <= a -> a + 8 <= alloc_ceiling ->
            (forall x, a <= x < a + 8 -> ~ (G_FAIL <= x < G_FAIL + 8)) ->
            word_mem (ms_segs B) mem a v -> word_mem (ms_segs B) mem' a v).
  { intros a v H0 H1 H2 Hw. apply (HsKindB.word_mem_munch _ _ mem mem' a v MU); [lia | lia | | exact Hw].
    intros x Hx. cbn [Frame.outside]. split; [lia|]. split; [exact (H2 x Hx) | exact I]. }
  split; [|split; [exact R1|split; [exact R2|split; [exact Hf|split; [exact ND|]]]]].
  - split; [|split; [|split]].
    + apply K; [unfold G_LIVE; lia | unfold G_LIVE; lia | unfold G_LIVE, G_FAIL; lia | exact W1].
    + apply K; [unfold G_PEAK; lia | unfold G_PEAK; lia | unfold G_PEAK, G_FAIL; lia | exact W2].
    + apply K; [unfold G_COUNT; lia | unfold G_COUNT; lia | unfold G_COUNT, G_FAIL; lia | exact W3].
    + exact HW.
  - eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact Hin|]. split; [|exact Hni].
    pose proof (HsKindB.block_low B API L A mem md (a - 16) (k + 16) 0 HM Hin ltac:(lia)) as B0.
    pose proof (HsKindB.block_low B API L A mem md (a - 16) (k + 16) 7 HM Hin ltac:(lia)) as B7.
    apply (HsKindB.word_mem_munch _ _ mem mem' (a - 16) k MU); [lia | lia | | exact Hw].
    intros x Hx. apply (crs_out_own GF L A mem md lo hi x HM Hlo ltac:(lia)).
    right. exists (a - 16), (k + 16). split; [exact Hin | lia].
Qed.

Lemma crs_guard_munch : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall L A mem md mem' lo hi, MR L A mem md -> Frame.munch [(lo, hi); (G_FAIL, G_FAIL + 8)] mem mem' ->
  alloc_ceiling <= lo -> guard_kept B mem mem'.
Proof.
  intros GF L A mem md mem' lo hi HM MU Hlo i Hi.
  assert (Ho : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hr. pose proof alloc_ceiling_val as Hac.
  apply (mbyte_munch (ms_segs B) _ mem mem' _ MU); [lia|].
  exact (crs_out_own GF L A mem md lo hi _ HM Hlo Hr (or_introl Ho)).
Qed.

Lemma crs_keep_of_mid : forall K sp L A mem md E L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' -> ublocks_kept L A A' (0, 0) -> keeps B L A mem mem' 0.
Proof.
  intros K sp L A mem md E L' A' mem' md' (_ & _ & _ & _ & _ & _ & _ & KB & _) UB a k i Hin Ha Hi.
  destruct (HsKindB.in_blocks L A a k Hin) as (p & Hp & ->).
  apply (KB p k i Hp); [|exact Hi]. apply (UB p k Hp). intros Ex. injection Ex as E1 _. exact (Ha E1).
Qed.

Lemma crs_room_down : forall b m n, 0 <= m -> room_slots (sb_malloc b m) n -> room_slots b n.
Proof.
  intros b m n Hm (Hn & HL & HC). unfold sb_malloc in HL, HC. cbn [sb_live sb_bytes sb_cap] in HL, HC.
  split; [exact Hn|]. split; [lia|].
  apply (CAPOK_mono (sb_cap b) (sb_cap b) (sb_bytes b + m + n) (sb_bytes b + n) n n); [lia | lia | lia | exact HC].
Qed.

Lemma crs_dec : preset_base64_decode_contract B API sb_form -> ms_segs B = rsegs -> errno_addr B + 4 <= alloc_ceiling ->
  forall L A regs mem md t tb slack Lam peak cnt bnd,
  call_pre_k B MR DEC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
  getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 (spZ regs) ->
  Mem.bytes_at rsegs mem t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  (forall i, 0 <= i < 8 -> writable_at (ms_segs B) mem (spZ regs + i)) ->
  spZ regs + 8 <= t \/ t + Z.of_nat (length tb) + 1 <= spZ regs ->
  ledger B L A mem Lam peak cnt cnt -> cnt + 1 < 2 ^ 64 ->
  res_ok_slots A bnd -> room_slots bnd (Z.of_nat (length tb) / 4 * 3 + 3 + 16) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PRESET_BASE64_DECODE) mem (seg_rom (ms_segs B))) md)
    (fun c' => exists L' A' regs' mem' md',
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
       ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
       (st_init_done A = true -> st_init_done A' = true) /\
       call_post_k B MR DEC_STACK L A regs mem md (fun a => alloc_statics a \/ spZ regs <= a < spZ regs + 8)
         L' A' regs' mem' md' /\
       (length (st_regions A) <= length (st_regions A'))%nat /\
       getr regs' 10 = Z_to_bv 64 0 /\ blocks L' A' = blocks L A /\ ublocks_kept L A A' (0, 0) /\
       (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (spZ regs + i) = mbyte (ms_segs B) mem (spZ regs + i)) /\
       ledger B L' A' mem' Lam peak (cnt + 1) (2 ^ 64 - 1) /\
       res_ok_slots A' bnd).
Proof.
  intros DEC SEG ERR L A regs mem md t tb slack Lam peak cnt bnd PRE RA R10 R11 TB NZ SL TBL TBLK WR DJ LG Hc1 RES ROOM.
  pose proof LG as (_ & _ & Hc0 & _).
  pose proof PRE as (_ & _ & _ & _ & H16 & _).
  eapply SR_bind.
  { apply (DEC L A regs mem md t (spZ regs) (zs tb) slack bnd Lam peak cnt cnt SEG ERR RA PRE R10 R11
      (crs_zs_nz tb NZ) (crs_zs_bytes tb)).
    - rewrite crs_zs_len. lia.
    - rewrite map_app, crs_map_zs. cbn [map]. rewrite <- app_assoc. cbn [app]. rewrite SEG. exact TB.
    - rewrite crs_zs_len. exact SL.
    - right. right. right. rewrite crs_zs_len. destruct TBLK as (pt & kt & H1 & H2 & H3).
      exists pt, kt. split; [exact H1|]. split; [exact H2 | lia].
    - split; [lia|]. unfold spZ. pose proof (zr_word (getr regs 2)) as Z0. unfold inr64 in Z0. lia.
    - Z.div_mod_to_equations. lia.
    - exact WR.
    - rewrite crs_zs_len. exact DJ.
    - exact LG.
    - exact RES.
    - unfold dec_size. rewrite crs_zs_len. exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & q & -> & RA' & GK & INIT & CP & LEN & KEEP & TXT & ARMS).
  destruct ARMS as [(_ & -> & R10' & BL & UB & LP & LG' & RES') | [(NC & _) | (bs & NC & _)]];
    [| exfalso; exact (NC eq_refl) | exfalso; exact (NC eq_refl)].
  apply SR_ret. exists L', A', regs', mem', md'.
  split; [reflexivity|]. split; [exact RA'|]. split; [exact GK|]. split; [exact INIT|].
  split.
  { destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP) as [MID RP]. apply (kb_post B API); [|exact RP].
    apply (kb_mid_E B API _ _ _ _ _ _ _ _ _ _ _ _ MID).
    intros a [Ha | [(Hq & _) | Ha]]; [left; exact Ha | exfalso; exact (Hq eq_refl) | right; exact Ha]. }
  split; [exact LEN|]. split; [exact R10'|]. split; [exact BL|]. split; [exact UB|]. split; [exact LP|].
  split; [rewrite Z.mod_small in LG' by lia; exact LG'|].
  exact RES'.
Qed.

Lemma crs_enc : preset_base64_encode_contract B API sb_form -> ms_segs B = rsegs -> errno_addr B + 4 <= alloc_ceiling ->
  forall L A regs mem md data len (bsd : list byte) Lam peak cnt bnd,
  call_pre_k B MR ENC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
  getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 len ->
  0 <= data < 2 ^ 64 -> data + len <= 2 ^ 64 -> Z.of_nat (length bsd) = len -> len <= 2 ^ 27 ->
  (forall i, 0 <= i < len -> mbyte (ms_segs B) mem (data + i) = Some (nth (Z.to_nat i) bsd (Z_to_bv 8 0))) ->
  (exists a k, In (a, k) (blocks L A) /\ a <= data /\ data + len <= a + k) ->
  ledger B L A mem Lam peak cnt cnt -> cnt + 1 < 2 ^ 64 ->
  res_ok_slots A bnd -> room_slots bnd ((len + 2) / 3 * 4 + 1 + 16) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PRESET_BASE64_ENCODE) mem (seg_rom (ms_segs B))) md)
    (fun c' => exists L' A' regs' mem' md',
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
       ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
       (st_init_done A = true -> st_init_done A' = true) /\
       call_post_k B MR ENC_STACK L A regs mem md alloc_statics L' A' regs' mem' md' /\
       (length (st_regions A) <= length (st_regions A'))%nat /\
       getr regs' 10 = Z_to_bv 64 0 /\ blocks L' A' = blocks L A /\ ublocks_kept L A A' (0, 0) /\
       ledger B L' A' mem' Lam peak (cnt + 1) (2 ^ 64 - 1) /\
       res_ok_slots A' bnd).
Proof.
  intros ENC SEG ERR L A regs mem md data len bsd Lam peak cnt bnd PRE RA R10 R11 HD HDL HL HL27 DATA BLK LG Hc1 RES ROOM.
  pose proof LG as (_ & _ & Hc0 & _).
  eapply SR_bind.
  { apply (ENC L A regs mem md data len (zs bsd) bnd Lam peak cnt cnt SEG ERR RA PRE R10 R11 HD HDL (crs_zs_bytes bsd)).
    - rewrite crs_zs_len. exact HL.
    - exact HL27.
    - intros i Hi. rewrite (DATA i Hi). rewrite crs_zs_nth. reflexivity.
    - right. left. exact BLK.
    - exact LG.
    - exact RES.
    - unfold enc_size. exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & q & -> & RA' & GK & INIT & CP & LEN & R10' & KEEP & UB & DAT & ARMS).
  destruct ARMS as [(_ & -> & RES' & BL & LG') | (NC & _)]; [| exfalso; exact (NC eq_refl)].
  apply SR_ret. exists L', A', regs', mem', md'.
  split; [reflexivity|]. split; [exact RA'|]. split; [exact GK|]. split; [exact INIT|].
  split.
  { destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP) as [MID RP]. apply (kb_post B API); [|exact RP].
    apply (kb_mid_E B API _ _ _ _ _ _ _ _ _ _ _ _ MID).
    intros a [[Ha | (Hq & _)] | (Hq & _)]; [exact Ha | exfalso; exact (Hq eq_refl) | exfalso; exact (Hq eq_refl)]. }
  split; [exact LEN|]. split; [exact R10'|]. split; [exact BL|]. split; [exact UB|].
  split; [rewrite Z.mod_small in LG' by lia; exact LG'|].
  exact RES'.
Qed.

Theorem check_reject_clean_starved_holds :
  ms_segs B = rsegs -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B MR -> ctx_owned B API ->
  fuzz_alloc_live_contract -> fuzz_alloc_fail_contract -> check_reject_clean_contract ->
  preset_base64_decode_contract B API sb_form -> preset_base64_encode_contract B API sb_form ->
  check_reject_clean_starved_contract B API.
Proof.
  intros SEG ERR GF AX CO FAL FAF CRC DEC ENC.
  unfold check_reject_clean_starved_contract.
  intros L A regs mem md t tb slack bd l bnd Lam peak cnt PRE R10 R11 R12 TB NZ SL TBL NW TBLK CAW BDL LG HC RA ROK ROOM.
  pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  assert (EK : CRCS_STK = 9216) by reflexivity.
  rewrite EK in HAC.
  destruct (kb_md B API L A mem md HM) as [Hh Hl0].
  assert (IL : img_low B).
  { apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia]. }
  assert (STK : Frame.stk rsegs mem (spZ regs - 9216) (spZ regs)).
  { pose proof (kb_stk B API IL CRCS_STK L A regs mem md PRE ltac:(rewrite EK; lia)) as K. rewrite SEG, EK in K. exact K. }
  assert (RA0 : ro_agree rsegs mem) by (rewrite <- SEG; exact RA).
  pose proof LG as ((W1 & W2 & W3 & W4) & LG1 & LG2 & LG3 & LGN & LGF).
  assert (LS0 : 0 <= lsum Lam).
  { apply crs_lsum. eapply Forall_impl; [|exact LGF]. intros [a k] (Hk & _). exact Hk. }
  assert (HLIVE : Mem.bytes_at rsegs mem G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam)))).
  { rewrite <- SEG. apply word_mem_le8; [exact W1 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia]. }
  assert (HCNT : Mem.bytes_at rsegs mem G_COUNT (Mem.le8 (Z_to_bv 64 cnt))).
  { rewrite <- SEG. apply word_mem_le8; [exact W3 | lia | unfold G_COUNT; lia | unfold G_COUNT; lia]. }
  assert (GIN : forall k, 0 <= k < 8 -> in_globals [(G_FAIL, 8); (G_LIVE, 24)] (G_FAIL + k)).
  { intros k Hk. exists G_FAIL, 8. split; [left; reflexivity | lia]. }
  assert (HFW : Mem.wr_at rsegs mem G_FAIL 8).
  { rewrite <- SEG. exact (globals_wr_at B API _ mem G_FAIL _ GF GIN W4). }
  pose proof TBLK as (pt & kt & Hpt & Hpt1 & Hpt2).
  pose proof (Mem.bytes_at_bound _ _ _ _ TB) as TBB. rewrite length_app in TBB. cbn [length] in TBB.
  assert (BKR : 4096 <= pt /\ pt + kt <= alloc_ceiling).
  { destruct (HsKindB.in_blocks L A pt kt Hpt) as (p & Hp & ->).
    exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p kt HM Hp). }
  assert (INIT0 : st_init_done A = true).
  { destruct (HsKindB.in_blocks L A pt kt Hpt) as (p & Hp & _). exact (YI04.init_done_of_block A (p, kt) HWF Hp). }
  assert (TW : t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) <= spZ regs - 9216).
  { destruct (crs_window (spZ regs) CRCS_STK t (t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack)) NW
      ltac:(lia) ltac:(rewrite EK; lia)) as [H|H]; rewrite EK in *; lia. }
  remember ((- (t + Z.of_nat (length tb) + 1)) mod 8) as r eqn:Er.
  assert (Hr : 0 <= r < 8) by (rewrite Er; apply Z.mod_pos_bound; lia).
  assert (Hr8 : (t + Z.of_nat (length tb) + 1 + r) mod 8 = 0).
  { rewrite Er. rewrite Z.add_mod_idemp_r by lia.
    replace (t + Z.of_nat (length tb) + 1 + - (t + Z.of_nat (length tb) + 1)) with 0 by lia. reflexivity. }
  remember (firstn (Z.to_nat r) slack) as slk eqn:Eslk.
  assert (SLK : Z.of_nat (length slk) = r) by (rewrite Eslk, firstn_length_le by lia; lia).
  assert (TB' : Mem.bytes_at rsegs mem t (tb ++ Z_to_bv 8 0 :: slk)).
  { rewrite SEG in TB. rewrite <- (firstn_skipn (Z.to_nat r) slack) in TB. rewrite <- Eslk in TB.
    replace (tb ++ Z_to_bv 8 0 :: slk ++ skipn (Z.to_nat r) slack)
      with ((tb ++ Z_to_bv 8 0 :: slk) ++ skipn (Z.to_nat r) slack) in TB by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app in TB. exact (proj1 TB). }
  assert (RM1 : room_slots bnd (Z.of_nat (length tb) / 4 * 3 + 3 + 16)).
  { unfold starved_ops in ROOM. cbn [hs_room] in ROOM. exact (proj1 ROOM). }
  eapply (kb_run B regs (Z_to_bv 64 CHECK_REJECT_CLEAN_STARVED) mem md
    (fun R pc' m' => R = crs_R1 regs (Z_to_bv 64 (lsum Lam)) /\ pc' = Z_to_bv 64 0x14e90 /\
       Step.rw_cells rsegs m' (spZ regs + -48)
         [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
          C8 (getr regs 1)] /\
       Mem.bytes_at rsegs m' G_FAIL (Mem.le8 (Z_to_bv 64 cnt)) /\
       Frame.munch [(spZ regs + -48, spZ regs); (G_FAIL, G_FAIL + 8)] mem m' /\ Frame.wmono rsegs mem m'));
    [exact Hh | exact Hl0 | |].
  { rewrite SEG. unfold CHECK_REJECT_CLEAN_STARVED, rmk. eapply Exec.evt_mono.
    - eapply (crs_seg1 FAL FAF); [exact STK | unfold spZ in *; lia | lia | exact HLIVE | exact HCNT | exact HFW |
        rewrite MState.unsigned_lit by lia; lia].
    - intros ms' (m' & -> & FR & BF & MU & WM). do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact FR|]. split; [exact BF|]. split; [exact MU | exact WM]. }
  intros R pc1 mem1 regs1 (-> & -> & FR1 & BF1 & MU1 & WM1) HG.
  assert (R1_1 : getr regs1 1 = Z_to_bv 64 0x13dcc) by (rewrite HG; reflexivity).
  assert (R1_2 : getr regs1 2 = Z_to_bv 64 (spZ regs + -48)) by (rewrite HG; reflexivity).
  assert (SP1 : spZ regs1 = spZ regs - 48).
  { unfold spZ at 1. rewrite R1_2, MState.unsigned_lit by lia. lia. }
  assert (MU1' : Frame.munch [(spZ regs - 48, spZ regs); (G_FAIL, G_FAIL + 8)] mem mem1).
  { replace (spZ regs - 48) with (spZ regs + -48) by lia. exact MU1. }
  assert (PRE1 : call_pre_k B MR DEC_STACK L A regs1 mem1 md).
  { apply (kb_pre_A B API CRCS_STK 48 DEC_STACK L A regs mem md regs1 mem1
      [(spZ regs - 48, spZ regs); (G_FAIL, G_FAIL + 8)] PRE).
    - lia.
    - unfold DEC_STACK, ALLOC_STACK. lia.
    - rewrite EK. unfold DEC_STACK, ALLOC_STACK. lia.
    - exact SP1.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - rewrite HG. reflexivity.
    - rewrite R1_1. vm_compute. reflexivity.
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hx'. cbn [Frame.outside]. split; [lia|]. split; [unfold G_FAIL; lia | exact I].
    - intros x Hx Ho. exact (crs_out_own GF L A mem md (spZ regs - 48) (spZ regs) x HM ltac:(lia) Hx Ho). }
  assert (RA1 : ro_agree rsegs mem1) by exact (crs_ro_munch mem mem1 _ _ RA0 MU1' ltac:(lia)).
  assert (WF1 : word_mem (ms_segs B) mem1 G_FAIL cnt).
  { rewrite SEG. pose proof (bytes_at_le8_word rsegs mem1 G_FAIL _ BF1) as H.
    rewrite MState.unsigned_lit in H by lia. exact H. }
  assert (LGa : ledger B L A mem1 Lam peak cnt cnt).
  { exact (crs_ledger_munch GF L A mem md mem1 _ _ Lam peak cnt _ cnt HM LG MU1' ltac:(lia) WF1 ltac:(lia)). }
  assert (GK1 : guard_kept B mem mem1) by exact (crs_guard_munch GF L A mem md mem1 _ _ HM MU1' ltac:(lia)).
  assert (MA1 : kb_mid B API CRCS_STK (spZ regs) L A mem md alloc_statics L A mem1 md).
  { apply (kb_mid_A B API IL CRCS_STK (spZ regs) L A mem md mem1 [(spZ regs - 48, spZ regs); (G_FAIL, G_FAIL + 8)]
      alloc_statics HM HWF HBD).
    - intros a [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha].
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hs He. cbn [Frame.outside]. rewrite EK in Hs. split; [lia|]. split; [|exact I].
      intros Hg. apply He. unfold alloc_statics. right. right. right. exact Hg.
    - intros x Hx Ho. exact (crs_out_own GF L A mem md (spZ regs - 48) (spZ regs) x HM ltac:(lia) Hx Ho). }
  assert (TB1 : Mem.bytes_at rsegs mem1 t (tb ++ Z_to_bv 8 0 :: slk)).
  { apply (bytes_at_transport rsegs _ mem mem1 t _ TB' MU1'). rewrite length_app. cbn [length disjoint_from].
    split; [lia|]. split; [|exact I].
    apply (crs_disj t (Z.of_nat (length tb + S (length slk))) G_FAIL (G_FAIL + 8)); [|lia|lia].
    intros x Hx Hg.
    destruct (Z_lt_le_dec x (t + Z.of_nat (length tb) + 1)) as [Hx1|Hx1].
    - exact (crs_blk_notG GF L A mem md pt kt x HM Hpt ltac:(lia) Hg).
    - pose proof (crs_align t (Z.of_nat (length tb)) r x Hr Hr8 ltac:(lia) Hg) as Hg'.
      exact (crs_blk_notG GF L A mem md pt kt (t + Z.of_nat (length tb)) HM Hpt ltac:(lia) Hg'). }
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  eapply SR_bind.
  { apply (crs_dec DEC SEG ERR L A regs1 mem1 md t tb slk Lam peak cnt bnd PRE1).
    - rewrite SEG. exact RA1.
    - rewrite HG. exact R10.
    - rewrite HG, SP1. transitivity (Z_to_bv 64 (spZ regs + -48)); [reflexivity | f_equal; lia].
    - exact TB1.
    - exact NZ.
    - rewrite SLK, Er. lia.
    - exact TBL.
    - exact TBLK.
    - intros i Hi. rewrite SEG, SP1. pose proof FR1 as [_ (_ & _ & WR)].
      replace (spZ regs - 48 + i) with (spZ regs + -48 + i) by lia. exact (WR i ltac:(cbn; lia)).
    - right. rewrite SP1. lia.
    - exact LGa.
    - lia.
    - exact ROK.
    - exact RM1. }
  intros c2 (L1 & A1 & regs2 & mem2 & md1 & -> & RA2 & GK2 & INIT2 & CP2 & LEN2 & R2_10 & BL2 & UB2 & LP2 & LG2' & RES2).
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP2) as [MD2 RP2].
  pose proof CP2 as (HM2 & HWF2 & HBD2 & _ & HPA2 & _ & _ & HFR2 & _ & _).
  rewrite SEG in RA2.
  assert (F2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 8368 <= a < spZ regs - 40) ->
    mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
    (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)).
  { intros a Ha Hn. apply HFR2.
    - left. exact Ha.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k, DEC_STACK, ALLOC_STACK. rewrite SP1. lia.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. rewrite SP1. lia. }
  assert (M1 : kb_mid B API CRCS_STK (spZ regs) L A mem md
      (fun a => alloc_statics a \/ (alloc_statics a \/ spZ regs1 <= a < spZ regs1 + 8)) L1 A1 mem2 md1).
  { apply (crs_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MA1 MD2).
    - rewrite SP1, EK. unfold DEC_STACK, ALLOC_STACK. lia.
    - rewrite SP1. lia.
    - rewrite EK. lia.
    - lia.
    - intros p n Hp _. exact Hp.
    - intros a _ Ho _. exact Ho.
    - intros a Ha Hn He Hw. rewrite SP1 in Hn. unfold DEC_STACK, ALLOC_STACK in Hn. rewrite EK in Ha.
      assert (Hd : spZ regs - 48 <= a < spZ regs - 40 \/ ~ (spZ regs - 8368 <= a < spZ regs - 40)) by lia.
      destruct Hd as [Hl|Hl].
      + rewrite SEG in Hw, LP2 |- *. apply (proj2 (crs_wr_hi mem2 a ltac:(lia))).
        apply (proj1 (crs_wr_hi mem1 a ltac:(lia))) in Hw.
        replace a with (spZ regs1 + (a - spZ regs1)) by lia. rewrite (LP2 (a - spZ regs1) ltac:(rewrite SP1; lia)).
        replace (spZ regs1 + (a - spZ regs1)) with a by lia. exact Hw.
      + exact (proj1 (proj2 (F2 a ltac:(lia) ltac:(lia))) Hw). }
  assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs + -48)
      [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
       C8 (getr regs 1)]).
  { apply (crs_rw_keep mem1 mem2 (spZ regs + -48) _ ltac:(lia) FR1). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    rewrite <- SEG. destruct (Z_lt_le_dec a (spZ regs - 40)) as [Hl|Hl].
    - replace a with (spZ regs1 + (a - spZ regs1)) by lia. apply LP2. rewrite SP1. lia.
    - exact (proj1 (F2 a ltac:(lia) ltac:(lia))). }
  assert (SV2 : forall k, callee_saved k ->
    getr regs2 (Z_to_bv 5 k) = getr (crs_R1 regs (Z_to_bv 64 (lsum Lam))) (Z_to_bv 5 k)).
  { intros k Hk. rewrite (RP2 k Hk). apply HG. }
  assert (Q2_2 : getr regs2 2 = Z_to_bv 64 (spZ regs + -48)) by exact (SV2 2 ltac:(unfold callee_saved; lia)).
  assert (SP2 : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite Q2_2, MState.unsigned_lit by lia; lia).
  assert (Q2_8 : getr regs2 8 = Z_to_bv 64 (lsum Lam)) by exact (SV2 8 ltac:(unfold callee_saved; lia)).
  assert (Q2_18 : getr regs2 18 = Z_to_bv 64 bd) by (rewrite <- R11; exact (SV2 18 ltac:(unfold callee_saved; lia))).
  assert (Q2_9 : getr regs2 9 = Z_to_bv 64 l) by (rewrite <- R12; exact (SV2 9 ltac:(unfold callee_saved; lia))).
  assert (SV2' : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs2 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
  { intros k Hk. rewrite (SV2 k ltac:(unfold callee_saved; lia)). apply crs_R1_saved. exact Hk. }
  pose proof M1 as (_ & _ & _ & _ & _ & _ & _ & _ & S1).
  assert (ST2 : Frame.stk rsegs mem2 (spZ regs - 9216) (spZ regs - 48)).
  { apply HsKindB.stk_of_writable; [lia | lia |]. intros a Ha. rewrite <- SEG. apply S1. left. rewrite EK. lia. }
  pose proof LG2' as ((V1 & V2 & V3 & V4) & _ & VC & _).
  assert (HLIVE2 : Mem.bytes_at rsegs mem2 G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam)))).
  { rewrite <- SEG. apply word_mem_le8; [exact V1 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia]. }
  assert (HCNT2 : Mem.bytes_at rsegs mem2 G_COUNT (Mem.le8 (Z_to_bv 64 (cnt + 1)))).
  { rewrite <- SEG. apply word_mem_le8; [exact V3 | lia | unfold G_COUNT; lia | unfold G_COUNT; lia]. }
  assert (HFW2 : Mem.wr_at rsegs mem2 G_FAIL 8).
  { rewrite <- SEG. exact (globals_wr_at B API _ mem2 G_FAIL _ GF GIN V4). }
  assert (FR2' : Step.rw_cells rsegs mem2 (bv_unsigned (getr regs2 2))
      [C8 (Z_to_bv 64 18446744073709551615); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
       C8 (getr regs 1)]).
  { rewrite SP2. replace (spZ regs - 48) with (spZ regs + -48) by lia. exact FR2. }
  destruct (Z.eq_dec bd 0) as [BD0 | BDN].
  - eapply (kb_run B regs2 (getr regs1 1) mem2 md1
      (fun R pc' m' => regs_preserved regs R /\ pc' = ret_pc (getr regs 1) /\
         Frame.munch [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)] mem2 m' /\ Frame.wmono rsegs mem2 m' /\
         Mem.bytes_at rsegs m' G_FAIL (Mem.le8 (Z_to_bv 64 18446744073709551615))));
      [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
    { rewrite SEG, R1_1. unfold rmk. eapply Exec.evt_mono.
      - eapply (crs_seg2_ret FAF CRC) with (lo := spZ regs - 9216) (count := Z_to_bv 64 (cnt + 1));
          [exact FR2' | rewrite SP2; exact ST2 | rewrite SP2; lia | lia | rewrite Q2_8; exact HLIVE2 | exact HCNT2 |
           exact HFW2 | rewrite MState.unsigned_lit by lia; lia | exact R2_10 | rewrite Q2_18, BD0; reflexivity].
      - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & BF & MU & WM).
        do 3 eexists. split; [reflexivity|]. split.
        + apply crs_rp;
            [ rewrite SP2; replace (spZ regs - 48 + 48) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
            | exact (SV2' 3 ltac:(lia)) | exact (SV2' 4 ltac:(lia)) | reflexivity | reflexivity | reflexivity | reflexivity
            | exact (SV2' 20 ltac:(lia)) | exact (SV2' 21 ltac:(lia)) | exact (SV2' 22 ltac:(lia))
            | exact (SV2' 23 ltac:(lia)) | exact (SV2' 24 ltac:(lia)) | exact (SV2' 25 ltac:(lia))
            | exact (SV2' 26 ltac:(lia)) | exact (SV2' 27 ltac:(lia)) ].
        + split; [reflexivity|].
          split; [rewrite SP2 in MU; eapply munch_weaken; [|exact MU]; unfold sub_fp, G_FAIL, G_FAIL_AT;
            cbn [outside]; intros x Hx; lia|].
          split; [exact WM | exact BF]. }
    intros R pc3 mem3 regs3 (RPR & -> & MU3 & WM3 & BF3) HG3.
    assert (MA2 : kb_mid B API CRCS_STK (spZ regs) L1 A1 mem2 md1 alloc_statics L1 A1 mem3 md1).
    { apply (kb_mid_A B API IL CRCS_STK (spZ regs) L1 A1 mem2 md1 mem3 [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)]
        alloc_statics HM2 HWF2 HBD2).
      - exact S1.
      - exact MU3.
      - rewrite SEG. exact WM3.
      - intros x Hx Hs He. cbn [Frame.outside]. rewrite EK in Hs. split; [lia|]. split; [|exact I].
        intros Hg. apply He. unfold alloc_statics. right. right. right. exact Hg.
      - intros x Hx Ho. exact (crs_out_own GF L1 A1 mem2 md1 (spZ regs - 64) (spZ regs) x HM2 ltac:(lia) Hx Ho). }
    assert (M2 : kb_mid B API CRCS_STK (spZ regs) L A mem md alloc_statics L1 A1 mem3 md1).
    { apply (crs_mid_E _ _ _ _ _ _ _ _ _ _ _ _ (crs_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 MA2
        ltac:(lia) ltac:(lia) ltac:(rewrite EK; lia) LEN2 ltac:(intros p n _ Hp; exact Hp)
        ltac:(intros a _ _ Ho; exact Ho) ltac:(intros a Ha Hn; exfalso; exact (Hn Ha)))).
      intros a Hn [[Ha | [Ha | Ha]] | Ha]; try exact Ha. exfalso. apply Hn. rewrite SP1 in Ha. rewrite EK. lia. }
    apply SR_ret. exists L1, A1, regs3, mem3, md1.
    split; [rewrite (kb_ret_pc _ HRA); reflexivity|].
    split; [rewrite SEG; exact (crs_ro_munch mem2 mem3 _ _ RA2 MU3 ltac:(lia))|].
    split.
    { intros i Hi. rewrite (crs_guard_munch GF L1 A1 mem2 md1 mem3 _ _ HM2 MU3 ltac:(lia) i Hi).
      rewrite (GK2 i Hi). exact (GK1 i Hi). }
    split; [apply (kb_post B API); [exact M2 | exact (kb_preserved_getr _ _ _ RPR HG3)]|].
    split; [intros _; apply INIT2; exact INIT0|].
    split; [exact BL2|].
    split; [exact (crs_keep_of_mid _ _ _ _ _ _ _ _ _ _ _ M2 UB2)|].
    split; [exact UB2|].
    split.
    { rewrite (proj2 (Z.eqb_eq bd 0) BD0).
      apply (crs_ledger_munch GF L1 A1 mem2 md1 mem3 _ _ Lam peak (cnt + 1) _ (2 ^ 64 - 1) HM2 LG2' MU3 ltac:(lia));
        [|lia].
      rewrite SEG. exact (bytes_at_le8_word rsegs mem3 G_FAIL _ BF3). }
    exact RES2.
  - destruct CAW as [(_ & E0 & _) | (bs & DBS & _ & EL & BBS)]; [exfalso; exact (BDN E0)|].
    destruct (BDL BDN) as (kb & Hkb & Hlk).
    pose proof LGF as LGF'. rewrite Forall_forall in LGF'.
    destruct (LGF' (bd, kb) Hkb) as (Hk0 & Hinb & _ & _). cbn [fst snd] in Hk0, Hinb.
    destruct (ledger_block_range B API L A mem md Lam peak cnt (2 ^ 64 - 1) bd kb HM LG Hkb) as (BR1 & BR2 & BR3).
    assert (Hbsl : (length bs <= length tb)%nat).
    { pose proof (crs_dec_len _ _ DBS) as H. rewrite crs_zs_len in H. exact H. }
    assert (RM2 : room_slots bnd ((l + 2) / 3 * 4 + 1 + 16)).
    { unfold starved_ops in ROOM. rewrite (proj2 (Z.eqb_neq bd 0) BDN) in ROOM. cbn [hs_room] in ROOM.
      apply (crs_room_down bnd (Z.of_nat (length tb) / 4 * 3 + 3 + 16)); [lia | exact (proj1 (proj2 ROOM))]. }
    eapply (kb_run B regs2 (getr regs1 1) mem2 md1
      (fun R pc' m' => (exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : word,
          R = mkR (Z_to_bv 64 0x13e00) (getr regs2 2) (getr regs2 3) (getr regs2 4) u0 u1 u2 (getr regs2 8)
            (getr regs2 9) (getr regs2 18) (getr regs2 9) u3 u4 u5 u6 u7 u8 (getr regs2 18) (Z_to_bv 64 0)
            (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25)
            (getr regs2 26) (getr regs2 27) u9 u10 u11 u12) /\
         pc' = Z_to_bv 64 0x14d10 /\
         Step.rw_cells rsegs m' (spZ regs + -48)
           [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
            C8 (getr regs 1)] /\
         Mem.bytes_at rsegs m' G_FAIL (Mem.le8 (Z_to_bv 64 (cnt + 1))) /\
         Frame.munch [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)] mem2 m' /\ Frame.wmono rsegs mem2 m'));
      [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
    { rewrite SEG, R1_1. unfold rmk. eapply Exec.evt_mono.
      - eapply (crs_seg2_enc FAF CRC) with (lo := spZ regs - 9216) (count := Z_to_bv 64 (cnt + 1));
          [exact FR2' | rewrite SP2; exact ST2 | rewrite SP2; lia | lia | rewrite Q2_8; exact HLIVE2 | exact HCNT2 |
           exact HFW2 | rewrite MState.unsigned_lit by lia; lia | rewrite MState.unsigned_lit by lia; lia | exact R2_10 |
           rewrite Q2_18, MState.unsigned_lit by lia; exact BDN].
      - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & m' & -> & FR & BF & MU & WM).
        do 3 eexists. split; [reflexivity|].
        split; [exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12; reflexivity|].
        split; [reflexivity|].
        split; [rewrite SP2 in FR; replace (spZ regs - 48) with (spZ regs + -48) in FR by lia; exact FR|].
        split; [exact BF|].
        split; [|exact WM].
        rewrite SP2 in MU. eapply munch_weaken; [|exact MU]. unfold sub_fp, G_FAIL, G_FAIL_AT. cbn [outside].
        intros x Hx. lia. }
    intros R pc4 mem4 regs4
      ((u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & ->) & -> & FR4 & BF4 & MU4 & WM4) HG4.
    assert (R4_1 : getr regs4 1 = Z_to_bv 64 0x13e00) by (rewrite HG4; reflexivity).
    assert (R4_2 : getr regs4 2 = getr regs2 2) by (rewrite HG4; reflexivity).
    assert (R4_10 : getr regs4 10 = Z_to_bv 64 bd) by (rewrite HG4; exact Q2_18).
    assert (R4_11 : getr regs4 11 = Z_to_bv 64 l) by (rewrite HG4; exact Q2_9).
    assert (R4_4 : getr regs4 4 = getr regs 4) by (rewrite HG4; exact (SV2' 4 ltac:(lia))).
    assert (SP4 : spZ regs4 = spZ regs - 48) by (unfold spZ at 1; rewrite R4_2; exact SP2).
    assert (MA2 : kb_mid B API CRCS_STK (spZ regs) L1 A1 mem2 md1 alloc_statics L1 A1 mem4 md1).
    { apply (kb_mid_A B API IL CRCS_STK (spZ regs) L1 A1 mem2 md1 mem4 [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)]
        alloc_statics HM2 HWF2 HBD2).
      - exact S1.
      - exact MU4.
      - rewrite SEG. exact WM4.
      - intros x Hx Hs He. cbn [Frame.outside]. rewrite EK in Hs. split; [lia|]. split; [|exact I].
        intros Hg. apply He. unfold alloc_statics. right. right. right. exact Hg.
      - intros x Hx Ho. exact (crs_out_own GF L1 A1 mem2 md1 (spZ regs - 64) (spZ regs) x HM2 ltac:(lia) Hx Ho). }
    assert (M2 : kb_mid B API CRCS_STK (spZ regs) L A mem md
        (fun a => (alloc_statics a \/ (alloc_statics a \/ spZ regs1 <= a < spZ regs1 + 8)) \/ alloc_statics a)
        L1 A1 mem4 md1).
    { exact (crs_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 MA2
        ltac:(lia) ltac:(lia) ltac:(rewrite EK; lia) LEN2 ltac:(intros p n _ Hp; exact Hp)
        ltac:(intros a _ _ Ho; exact Ho) ltac:(intros a Ha Hn; exfalso; exact (Hn Ha))). }
    pose proof M2 as (HM4 & _ & _ & _ & _ & _ & _ & _ & S4).
    assert (RA4 : ro_agree rsegs mem4) by exact (crs_ro_munch mem2 mem4 _ _ RA2 MU4 ltac:(lia)).
    assert (GK4 : guard_kept B mem2 mem4) by exact (crs_guard_munch GF L1 A1 mem2 md1 mem4 _ _ HM2 MU4 ltac:(lia)).
    assert (LG4 : ledger B L1 A1 mem4 Lam peak (cnt + 1) (cnt + 1)).
    { apply (crs_ledger_munch GF L1 A1 mem2 md1 mem4 _ _ Lam peak (cnt + 1) _ (cnt + 1) HM2 LG2' MU4 ltac:(lia));
        [|lia].
      rewrite SEG. pose proof (bytes_at_le8_word rsegs mem4 G_FAIL _ BF4) as H.
      rewrite MState.unsigned_lit in H by lia. exact H. }
    assert (KP4 : keeps B L A mem mem4 0) by exact (crs_keep_of_mid _ _ _ _ _ _ _ _ _ _ _ M2 UB2).
    assert (PRE4 : call_pre_k B MR ENC_STACK L1 A1 regs4 mem4 md1).
    { unfold call_pre_k.
      split; [exact HM4|]. split; [exact HWF2|]. split; [exact HBD2|].
      split; [rewrite R4_1; vm_compute; reflexivity|].
      split; [rewrite SP4; Z.div_mod_to_equations; lia|].
      split; [rewrite SP4; unfold ENC_STACK, ALLOC_STACK; lia|].
      split; [rewrite SP4; lia|].
      split; [intros a Ha; apply S4; left; rewrite SP4 in Ha; unfold ENC_STACK, ALLOC_STACK in Ha; rewrite EK; lia|].
      split; [rewrite R4_4; exact HTP|].
      split; [intros a Ha; apply S4; right; exact Ha|].
      intros Hf. rewrite (INIT2 INIT0) in Hf. discriminate. }
    change (Z_to_bv 64 0x14d10) with (Z_to_bv 64 PRESET_BASE64_ENCODE).
    eapply SR_bind.
    { apply (crs_enc ENC SEG ERR L1 A1 regs4 mem4 md1 bd l (bz bs) Lam peak (cnt + 1)
        bnd PRE4).
      - rewrite SEG. exact RA4.
      - exact R4_10.
      - exact R4_11.
      - lia.
      - lia.
      - unfold bz. rewrite length_map. lia.
      - lia.
      - intros i Hi.
        replace (bd + i) with (bd - 16 + (i + 16)) by lia.
        rewrite (KP4 (bd - 16) (kb + 16) (i + 16) Hinb ltac:(lia) ltac:(lia)).
        replace (bd - 16 + (i + 16)) with (bd + Z.of_nat (Z.to_nat i)) by lia.
        destruct BBS as (_ & _ & HB).
        change (mbyte (ms_segs B) mem (bd + Z.of_nat (Z.to_nat i)))
          with (Mem.mrd (ms_segs B) mem (Mem.wa (bd + Z.of_nat (Z.to_nat i)))).
        rewrite (HB (Z.to_nat i) ltac:(unfold bz; rewrite length_map; lia)).
        apply nth_error_nth'. unfold bz. rewrite length_map. lia.
      - exists (bd - 16), (kb + 16). rewrite BL2. split; [exact Hinb | lia].
      - exact LG4.
      - lia.
      - exact RES2.
      - exact RM2. }
    intros c5 (L2 & A2 & regs5 & mem5 & md2 & -> & RA5 & GK5 & INIT5 & CP5 & LEN5 & R5_10 & BL5 & UB5 & LG5 & RES5).
    destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP5) as [MD5 RP5].
    pose proof CP5 as (HM5 & HWF5 & HBD5 & _ & HPA5 & _ & _ & HFR5 & _ & _).
    rewrite SEG in RA5.
    assert (F5 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 8304 <= a < spZ regs - 48) ->
      mbyte (ms_segs B) mem5 a = mbyte (ms_segs B) mem4 a /\
      (writable_at (ms_segs B) mem4 a <-> writable_at (ms_segs B) mem5 a)).
    { intros a Ha Hn. apply HFR5.
      - left. exact Ha.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM4 Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM5 Ho). lia.
      - unfold scratch_k, ENC_STACK, ALLOC_STACK. rewrite SP4. lia.
      - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
    assert (M3 : kb_mid B API CRCS_STK (spZ regs) L A mem md
        (fun a => ((alloc_statics a \/ (alloc_statics a \/ spZ regs1 <= a < spZ regs1 + 8)) \/ alloc_statics a) \/
                  alloc_statics a) L2 A2 mem5 md2).
    { apply (crs_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M2 MD5).
      - rewrite SP4, EK. unfold ENC_STACK, ALLOC_STACK. lia.
      - rewrite SP4. lia.
      - rewrite EK. lia.
      - exact LEN2.
      - intros p n Hp _. apply (UB2 p n Hp). intros Ex. injection Ex as E1 _.
        pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as RR. lia.
      - intros a Ha Ho _. exact (crs_own_mid AX CO L A mem md L1 A1 mem4 md1 a HM HM4 Ha Ho).
      - intros a Ha Hn He Hw. rewrite SP4 in Hn. unfold ENC_STACK, ALLOC_STACK in Hn. rewrite EK in Ha.
        exact (proj1 (proj2 (F5 a ltac:(lia) ltac:(lia))) Hw). }
    assert (FR5 : Step.rw_cells rsegs mem5 (spZ regs + -48)
        [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
         C8 (getr regs 1)]).
    { apply (crs_rw_keep mem4 mem5 (spZ regs + -48) _ ltac:(lia) FR4). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      rewrite <- SEG. exact (proj1 (F5 a ltac:(lia) ltac:(lia))). }
    assert (SV5 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs5 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
    { intros k Hk. rewrite (RP5 k ltac:(unfold callee_saved; lia)), HG4, crs_R4_saved by exact Hk. exact (SV2' k Hk). }
    assert (Q5_2 : getr regs5 2 = getr regs2 2).
    { transitivity (getr regs4 2); [exact (RP5 2 ltac:(unfold callee_saved; lia)) | exact R4_2]. }
    assert (SP5 : bv_unsigned (getr regs5 2) = spZ regs - 48) by (rewrite Q5_2; exact SP2).
    assert (Q5_8 : getr regs5 8 = Z_to_bv 64 (lsum Lam)).
    { transitivity (getr regs4 8); [exact (RP5 8 ltac:(unfold callee_saved; lia)) | rewrite HG4; exact Q2_8]. }
    pose proof LG5 as ((X1 & X2 & X3 & X4) & _ & XC & _).
    assert (HLIVE5 : Mem.bytes_at rsegs mem5 G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam)))).
    { rewrite <- SEG. apply word_mem_le8; [exact X1 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia]. }
    assert (HCNT5 : Mem.bytes_at rsegs mem5 G_COUNT (Mem.le8 (Z_to_bv 64 (cnt + 1 + 1)))).
    { rewrite <- SEG. apply word_mem_le8; [exact X3 | lia | unfold G_COUNT; lia | unfold G_COUNT; lia]. }
    assert (HFW5 : Mem.wr_at rsegs mem5 G_FAIL 8).
    { rewrite <- SEG. exact (globals_wr_at B API _ mem5 G_FAIL _ GF GIN X4). }
    pose proof M3 as (_ & _ & _ & _ & _ & _ & _ & _ & S5).
    eapply (kb_run B regs5 (getr regs4 1) mem5 md2
      (fun R pc' m' => regs_preserved regs R /\ pc' = ret_pc (getr regs 1) /\
         Frame.munch [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)] mem5 m' /\ Frame.wmono rsegs mem5 m' /\
         Mem.bytes_at rsegs m' G_FAIL (Mem.le8 (Z_to_bv 64 18446744073709551615))));
      [exact (proj1 (kb_md B API _ _ _ _ HM5)) | exact (proj2 (kb_md B API _ _ _ _ HM5)) | |].
    { rewrite SEG, R4_1. unfold rmk. eapply Exec.evt_mono.
      - eapply (crs_seg3 FAL FAF) with (count := Z_to_bv 64 (cnt + 1 + 1));
          [rewrite SP5; replace (spZ regs - 48) with (spZ regs + -48) by lia; exact FR5 | rewrite Q5_8; exact HLIVE5 |
           exact HCNT5 | exact HFW5 | rewrite MState.unsigned_lit by lia; lia | exact R5_10 | rewrite SP5; lia].
      - intros ms' (a1' & m' & -> & BF & MU & WM). do 3 eexists. split; [reflexivity|]. split.
        + apply crs_rp;
            [ rewrite SP5; replace (spZ regs - 48 + 48) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
            | exact (SV5 3 ltac:(lia)) | exact (SV5 4 ltac:(lia)) | reflexivity | reflexivity | reflexivity | reflexivity
            | exact (SV5 20 ltac:(lia)) | exact (SV5 21 ltac:(lia)) | exact (SV5 22 ltac:(lia))
            | exact (SV5 23 ltac:(lia)) | exact (SV5 24 ltac:(lia)) | exact (SV5 25 ltac:(lia))
            | exact (SV5 26 ltac:(lia)) | exact (SV5 27 ltac:(lia)) ].
        + split; [reflexivity|].
          split; [eapply munch_weaken; [|exact MU]; unfold sub_fp, G_FAIL, G_FAIL_AT; cbn [outside]; intros x Hx; lia|].
          split; [exact WM | exact BF]. }
    intros R pc6 mem6 regs6 (RPR & -> & MU6 & WM6 & BF6) HG6.
    assert (MA3 : kb_mid B API CRCS_STK (spZ regs) L2 A2 mem5 md2 alloc_statics L2 A2 mem6 md2).
    { apply (kb_mid_A B API IL CRCS_STK (spZ regs) L2 A2 mem5 md2 mem6 [(spZ regs - 64, spZ regs); (G_FAIL, G_FAIL + 8)]
        alloc_statics HM5 HWF5 HBD5).
      - exact S5.
      - exact MU6.
      - rewrite SEG. exact WM6.
      - intros x Hx Hs He. cbn [Frame.outside]. rewrite EK in Hs. split; [lia|]. split; [|exact I].
        intros Hg. apply He. unfold alloc_statics. right. right. right. exact Hg.
      - intros x Hx Ho. exact (crs_out_own GF L2 A2 mem5 md2 (spZ regs - 64) (spZ regs) x HM5 ltac:(lia) Hx Ho). }
    assert (M4 : kb_mid B API CRCS_STK (spZ regs) L A mem md alloc_statics L2 A2 mem6 md2).
    { apply (crs_mid_E _ _ _ _ _ _ _ _ _ _ _ _ (crs_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M3 MA3
        ltac:(lia) ltac:(lia) ltac:(rewrite EK; lia) ltac:(lia) ltac:(intros p n _ Hp; exact Hp)
        ltac:(intros a _ _ Ho; exact Ho) ltac:(intros a Ha Hn; exfalso; exact (Hn Ha)))).
      intros a Hn [[[[Ha | [Ha | Ha]] | Ha] | Ha] | Ha]; try exact Ha.
      exfalso. apply Hn. rewrite SP1 in Ha. rewrite EK. lia. }
    assert (UB6 : ublocks_kept L A A2 (0, 0)).
    { intros q k Hq Hne. assert (Hq1 : In (q, k) (user_blocks A1)) by exact (UB2 q k Hq Hne).
      apply (UB5 q k Hq1). rewrite (HPA2 q k Hq Hq1). exact Hne. }
    apply SR_ret. exists L2, A2, regs6, mem6, md2.
    split; [rewrite (kb_ret_pc _ HRA); reflexivity|].
    split; [rewrite SEG; exact (crs_ro_munch mem5 mem6 _ _ RA5 MU6 ltac:(lia))|].
    split.
    { intros i Hi. rewrite (crs_guard_munch GF L2 A2 mem5 md2 mem6 _ _ HM5 MU6 ltac:(lia) i Hi).
      rewrite (GK5 i Hi), (GK4 i Hi), (GK2 i Hi). exact (GK1 i Hi). }
    split; [apply (kb_post B API); [exact M4 | exact (kb_preserved_getr _ _ _ RPR HG6)]|].
    split; [intros _; apply INIT5; apply INIT2; exact INIT0|].
    split; [rewrite BL5; exact BL2|].
    split; [exact (crs_keep_of_mid _ _ _ _ _ _ _ _ _ _ _ M4 UB6)|].
    split; [exact UB6|].
    split.
    { rewrite (proj2 (Z.eqb_neq bd 0) BDN). replace (cnt + 2) with (cnt + 1 + 1) by lia.
      apply (crs_ledger_munch GF L2 A2 mem5 md2 mem6 _ _ Lam peak (cnt + 1 + 1) _ (2 ^ 64 - 1) HM5 LG5 MU6 ltac:(lia));
        [|lia].
      rewrite SEG. exact (bytes_at_le8_word rsegs mem6 G_FAIL _ BF6). }
    exact RES5.
Qed.

End S.
