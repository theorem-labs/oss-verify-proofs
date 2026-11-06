From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_online_c check_state_online_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_state_online_contract_F (image A, entry 0x8520c, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportList.v, slots 4074-4086, AF_check_state_online = 0x3fa8):
     0x8520c-0x85210  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85214-0x85218  auipc a0; addi a0,a0,..: a0 = 0x5df160 = TA_M (listing A_OBJ 8).
     0x8521c          lw a1,16(a0): a1 = the 4-byte load at 0x5df170 = M.e2_acked, sign-extended.
     0x85220          beqz a1, 0x85238.
     0x85224          lw a0,20(a0): a0 = the 4-byte load at 0x5df174 = M.e1_us, sign-extended.
     0x85228          beqz a0, 0x85238.
     0x8522c-0x85234  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x85238 / 0x8523c (TS___asan_handle_no_return, TS_abort) is never reached: the model premise
   check_state_online_m Bw = Some (Bw', tt) gives M_e2_acked Bw <> 0, M_e1_us Bw <> 0 and Bw' = Bw; by the world
   relation the four bytes at 0x5df170 are sub Bw A_M_e2_acked 4 and those at 0x5df174 are sub Bw A_M_e1_us 4
   (tw_bytes_at), so the loaded values are Z_to_bv 64 (M_e2_acked Bw) and Z_to_bv 64 (M_e1_us Bw) (lw_world), two
   32-bit signed values that are not 0, and each beqz falls through.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (TMAP_A_kept). *)

Theorem check_state_online_holds_F : check_state_online_contract_F.
Proof.
  unfold check_state_online_contract_F, CHECK_STATE_ONLINE, CHECK_STATE_ONLINE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RE2 RE1.
  (* the model: M.e2_acked <> 0, M.e1_us <> 0 and Bw' = Bw (fuzz_transport.c:503-504) *)
  assert (HE : TW.M_e2_acked Bw <> 0 /\ TW.M_e1_us Bw <> 0 /\ Bw' = Bw).
  { unfold TC.check_state_online_m, TC.truth in HM.
    destruct (Z.eqb_spec (TW.M_e2_acked Bw) 0) as [E2|E2]; cbn [negb orb] in HM; [discriminate HM|].
    destruct (Z.eqb_spec (TW.M_e1_us Bw) 0) as [E1|E1]; cbn [negb orb] in HM; [discriminate HM|].
    split; [exact E2|]. split; [exact E1|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HE as (HE2 & HE1 & ->). clear HM.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_e2_acked) as R2.
  change (TW.s32_at Bw TW.A_M_e2_acked) with (TW.M_e2_acked Bw) in R2.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_e1_us) as R1.
  change (TW.s32_at Bw TW.A_M_e1_us) with (TW.M_e1_us Bw) in R1.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  rewrite check_state_online_e2_at in RE2. rewrite check_state_online_e1_at in RE1.
  (* the 4 bytes of M.e2_acked and of M.e1_us, as raw memory *)
  assert (L2 : length (TW.sub Bw TW.A_M_e2_acked 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_e2_acked, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_M_e2_acked, TW.OFF_M, TW.W_LEN. lia. }
  assert (L1 : length (TW.sub Bw TW.A_M_e1_us 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_e1_us, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_M_e1_us, TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 16 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF2.
  change (TA_M + 16) with 6156656 in BF2. change (TW.OFF_M + 16) with TW.A_M_e2_acked in BF2.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 20 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF1.
  change (TA_M + 20) with 6156660 in BF1. change (TW.OFF_M + 20) with TW.A_M_e1_us in BF1.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj (conj BF2 BF1) I) as BFC. clear BF2 BF1.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x8520c-0x85210: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [[BF2 BF1] _].
  pose proof (bytes_tp m m0 _ _ 6156656 (TW.sub Bw TW.A_M_e2_acked 4) MU1 ltac:(rewrite L2; lia) BF2) as BF2'.
  pose proof (bytes_tp m m0 _ _ 6156660 (TW.sub Bw TW.A_M_e1_us 4) MU1 ltac:(rewrite L1; lia) BF1) as BF1'.
  clear BF2 BF1.
  assert (RD2 : ov_read_bytes rsegs m0 (wa 6156656) 4 = Some (TW.sub Bw TW.A_M_e2_acked 4)).
  { replace (wa 6156656) with (wa (6156656 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156656 _ 0 4 BF2' ltac:(lia)) by (rewrite L2; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L2. lia. }
  clear BF2'.
  (* 0x85214-0x8521c: a0 = 0x5df160; a1 = M.e2_acked *)
  step. step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_e2_acked) with (TW.M_e2_acked Bw).
  clear RD2.
  (* 0x85220: beqz a1; the branch to the trap path needs M.e2_acked = 0 *)
  step.
  if_cases K2; [exfalso; zify_cond K2; first [ lia | (Z.div_mod_to_equations; lia) ] |].
  assert (RD1 : ov_read_bytes rsegs m0 (wa 6156660) 4 = Some (TW.sub Bw TW.A_M_e1_us 4)).
  { replace (wa 6156660) with (wa (6156660 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156660 _ 0 4 BF1' ltac:(lia)) by (rewrite L1; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L1. lia. }
  clear BF1'.
  (* 0x85224: a0 = M.e1_us *)
  step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_e1_us) with (TW.M_e1_us Bw).
  clear RD1.
  (* 0x85228: beqz a0; the branch to the trap path needs M.e1_us = 0 *)
  step.
  if_cases K1; [exfalso; zify_cond K1; first [ lia | (Z.div_mod_to_equations; lia) ] |].
  (* 0x8522c-0x85234: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU1|].
  split; [match goal with WM' : wmono rsegs m m0 |- _ => exact WM' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (@TMAP_A_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_state_online_holds_F.
