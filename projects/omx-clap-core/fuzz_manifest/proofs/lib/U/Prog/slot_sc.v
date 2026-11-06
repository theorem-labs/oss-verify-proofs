From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem expected_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import fuzz_alloc_live_c fuzz_alloc_peak_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_bounded_alloc_c check_as_written_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sl_s1 : sl_s1_stmt.
Proof.
  unfold sl_s1_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m un
    -> HU.
  do 4 zstep.
  replace (un + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z]. rewrite Z.add_0_r.
  apply evt_done. eexists. reflexivity.
Qed.

Lemma sl_s4 : fuzz_alloc_peak_contract -> check_bounded_alloc_contract -> check_as_written_contract ->
  check_reject_clean_contract -> sl_s4_stmt.
Proof.
  intros PEAK CBA CAW CRC. unfold sl_s4_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo un ua ta live peak tb ts ub us -> -> -> -> -> HLU HU HPK HLV HPL HT HUs HTa HUa HLT HP HMI ST LO GLO OT OU OP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 peak) as Rpk. unfold bv_modulus in Rpk.
  pose proof (bv_unsigned_in_range 64 live) as Rlv. unfold bv_modulus in Rlv.
  assert (TAR : ta + 1 <= 2 ^ 64).
  { destruct HT as [(_ & HT1 & _) _]. rewrite length_app in HT1. cbn [length] in HT1. lia. }
  assert (UAR : ua + 1 <= 2 ^ 64).
  { destruct HUs as [(_ & HU1 & _) _]. rewrite length_app in HU1. cbn [length] in HU1. lia. }
  assert (UTA : bv_unsigned (Z_to_bv 64 ta) = ta) by (apply unsigned_lit; lia).
  assert (UUA : bv_unsigned (Z_to_bv 64 ua) = ua) by (apply unsigned_lit; lia).
  assert (UUN : bv_unsigned (Z_to_bv 64 un) = un) by (apply unsigned_lit; lia).
  do 2 zstep.
  eapply evt_cut; [eapply PEAK; exact HPK|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13054)) with (Z_to_bv 64 0x13054) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 3 zstep.
  eapply evt_cut.
  { eapply CBA.
    - rewrite UUN. lia.
    - rewrite UUN. rewrite unsigned_lit by lia. lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13060)) with (Z_to_bv 64 0x13060) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 4 zstep.
  eapply evt_cut.
  { eapply CAW with (lo := lo) (tb := tb) (ts := ts) (ub := ub) (us := us);
      unfold CHECK_AS_WRITTEN_K, EXPECTED_K, off_stack in *; rewrite ?UTA, ?UUA;
      first [ assumption | reflexivity | lia ]. }
  intros ms' PO. unfold kret in PO.
  destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  m2 & E & MU2 & WM2 & MI2 & ST2 & _).
  subst ms'.
  assert (MUA : munch [(bv_unsigned sp - 288, bv_unsigned sp)] m m2) by exact MU2.
  clear MU2.
  replace (ret_pc (Z_to_bv 64 0x13070)) with (Z_to_bv 64 0x13070) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (HLV2 : bytes_at rsegs m2 0x2f620 (le8 live)).
  { eapply bytes_at_transport; [exact HLV | exact MUA |]. cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
  do 2 zstep.
  eapply evt_cut.
  { eapply CRC with (lo := lo).
    - exact HLV2.
    - exact MI2.
    - exact ST2.
    - unfold CHECK_REJECT_CLEAN_FRAME. lia.
    - left. unfold G_LIVE, CHECK_REJECT_CLEAN_FRAME. lia. }
  intros ms' (t0''' & t1''' & t2''' & a0''' & a1''' & a2''' & a3''' & a4''' & a5''' & a6''' & a7''' & t3''' & t4''' & t5''' &
              t6''' & m3 & E & MU3 & WM3 & MI3 & ST3).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13078)) with (Z_to_bv 64 0x13078) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 3 zstep.
  apply evt_done.
  exists t0''', t1''', t2''', a2''', a3''', a4''', a5''', a6''', a7''', t3''', t4''', t5''', t6''', m3.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [|exact MU3].
    intros x Hx. cbn in *. unfold CHECK_REJECT_CLEAN_FRAME in *. lia. }
  split; [eapply wmono_trans; [exact WM2 | exact WM3]|].
  split; [exact MI3 | exact ST3].
Qed.

Lemma sl_s5 : sl_s5_stmt.
Proof. unfold sl_s5_stmt. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma sl_s6 : sl_s6_stmt.
Proof. unfold sl_s6_stmt. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma sl_s7 : sl_s7_stmt.
Proof. unfold sl_s7_stmt. intros. do 2 zstep. apply evt_done. reflexivity. Qed.
