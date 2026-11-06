From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac KindB CrtRun rec_calls_equal_c strcmp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma calls_at_norm : forall m lo hi a cs, ro_agree rsegs m -> calls_at m lo hi a cs ->
  calls_at (normalize rsegs m) lo hi a cs.
Proof.
  intros m lo hi a cs RO [Hl H]. split; [exact Hl|]. intros i e E.
  destruct (H i e E) as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [apply bytes_at_normalize; assumption|]. split; [exact H4|].
  intros k p Ek. destruct (H5 k p Ek) as (P1 & P2 & P3 & P4).
  split; [apply bytes_at_normalize; assumption|]. split; [apply bytes_at_normalize; assumption|].
  split; assumption.
Qed.

Lemma crt_s5 : rec_calls_equal_contract -> strcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo q : Z) (ca cb : list rc_entry) (rpw : word)
    (sx sy : list byte),
  s5 = Z_to_bv 64 0x33d48 -> s6 = Z_to_bv 64 0x34108 -> s0 = Z_to_bv 64 (Z.of_nat (length ca)) ->
  s8 = sx32 (Z_to_bv 64 q) ->
  ro_agree rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> 2 ^ 20 <= lo -> bv_unsigned sp + 904 <= 2 ^ 64 ->
  bytes_at rsegs m 212304 (le4 (Z_to_bv 64 (Z.of_nat (length cb)))) -> (length cb <= 16)%nat ->
  calls_at m (bv_unsigned sp - REC_CALLS_EQUAL_FRAME) (bv_unsigned sp) (bv_unsigned sp + 8) ca ->
  calls_at m (bv_unsigned sp - REC_CALLS_EQUAL_FRAME) (bv_unsigned sp) 212312 cb ->
  calls_eqb ca cb = true ->
  bytes_at rsegs m 213224 (le8 rpw) -> bv_unsigned rpw <> 0 ->
  bytes_at rsegs m (bv_unsigned rpw) (sx ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sx ->
  bv_unsigned rpw + Z.of_nat (length sx) + 1 <= lo ->
  bytes_at rsegs m (bv_unsigned s1) (sy ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sy ->
  bv_unsigned s1 + Z.of_nat (length sy) + 1 <= lo ->
  sx = sy ->
  bytes_at rsegs m 0x34108 (le4 (Z_to_bv 64 q)) ->
  bytes_at rsegs m 213240 (le8 s9) -> bytes_at rsegs m 213248 (le8 s7) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x14d80) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (bv_unsigned sp + 8)) s0
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - REC_CALLS_EQUAL_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d30) fc None m (seg_rom rsegs)).
Proof.
  intros RCE SCMP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo q ca cb rpw sx sy -> -> -> -> RO ST LO LOI SPT HN NB CA CB EQB HR RNZ HX NX LX HY NY LY XY HQ HS HH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold REC_CALLS_EQUAL_FRAME in CA, CB |- *.
  pose proof HN as HN'. apply bytes_ro4 in HN'.
  do 5 zstep.
  rewrite (sx32_small (Z.of_nat (length cb))) by lia.
  eapply evt_cut.
  { apply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO |].
    eapply (RCE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo ca cb).
    - apply mem_inv_normalize.
    - apply stk_normalize; [exact ST | lia].
    - unfold REC_CALLS_EQUAL_FRAME; lia.
    - reflexivity.
    - reflexivity.
    - apply calls_at_norm; [exact RO|]. rewrite unsigned_lit by lia. exact CA.
    - apply calls_at_norm; [exact RO|]. rewrite unsigned_lit by lia. exact CB. }
  intros ms1 (s0' & Q0 & REL & ROS).
  destruct Q0 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & -> & MU0 & WM0 & MI0 & ST0).
  apply ms_rel_MS in REL. destruct REL as [E1 MREL]. rewrite E1. clear E1.
  set (m1 := ms_mem ms1) in *.
  assert (MU1 : munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1)
    by exact (munch_rel rsegs _ m (normalize rsegs m) m1 m0' (mem_rel_normalize rsegs m RO) MREL ROS MU0).
  assert (WM1 : wmono rsegs m m1)
    by exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' (mem_rel_normalize rsegs m RO) MREL ROS WM0).
  assert (RO1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs m m1 RO ROS).
  rewrite EQB.
  replace (ret_pc (Z_to_bv 64 85316)) with (Z_to_bv 64 85316) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  clear CA CB ST HN HN' MU0 WM0 MI0 ST0 MREL ROS.
  apply bytes_ro8 in HR, HS, HH. apply bytes_ro4 in HQ.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m1) as MUR.
  transport_after_call rsegs m m1 MU1 WM1.
  zstep. if_false.
  zstep. zstep. if_false_by (proj2 (Z.eqb_neq _ _) RNZ).
  do 2 zstep.
  eapply evt_cut.
  { eapply (SCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sx sy); eassumption. }
  intros ms2 (r & x11 & x12 & x13 & -> & Hr).
  assert (R0 : r = Z_to_bv 64 0) by (apply Hr; exact XY). subst r.
  replace (ret_pc (Z_to_bv 64 85336)) with (Z_to_bv 64 85336) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. if_false.
  zstep. zstep. if_false.
  zstep. zstep. if_false.
  zstep. zstep. if_false.
  do 3 zstep.
  apply evt_done. do 13 eexists. exists m1. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1 | exact RO1].
Qed.
