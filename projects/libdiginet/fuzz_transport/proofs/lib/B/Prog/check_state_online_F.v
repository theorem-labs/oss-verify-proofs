From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_online_c check_state_online_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_state_online_contract_F (image B, entry 0x85320, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportBList.v, slots 4128-4141, AF_check_state_online = 0x4080):
     0x85320-0x85324  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85328-0x8532c  auipc a0; addi a0,a0,..: a0 = 0x5dede0 = TB_M (listing A_OBJ 8).
     0x85330          lw a1,16(a0): a1 = the 4-byte load at 0x5dedf0 = M.e2_acked, sign-extended.
     0x85334          beqz a1, 0x8534c.
     0x85338          lw a0,20(a0): a0 = the 4-byte load at 0x5dedf4 = M.e1_us, sign-extended.
     0x8533c          beqz a0, 0x8534c.
     0x85340-0x85348  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x8534c / 0x85350 / 0x85354 (TB___asan_handle_no_return, TB_abort, then the unimp word 0xc0001073)
   is never reached: the model premise check_state_online_m Bw = Some (Bw', tt) gives M_e2_acked Bw <> 0,
   M_e1_us Bw <> 0 and Bw' = Bw; by the world relation the four bytes at 0x5dedf0 are sub Bw A_M_e2_acked 4 and those
   at 0x5dedf4 are sub Bw A_M_e1_us 4 (tw_bytes_at), so the loaded values are Z_to_bv 64 (M_e2_acked Bw) and
   Z_to_bv 64 (M_e1_us Bw) (lw_world), two 32-bit signed values (s32_range) that are not 0, and each beqz falls
   through. The unimp word at 0x85354 is reached only from the abort call at 0x85350, so the same two facts rule it
   out. The function has no UBSan check of its own, and the statement has no alignment or range premise
   (lib/U/Prog/T/check_state_online_c.v has none either).

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (TMAP_B_kept). *)

(* A world bytes_at fact survives a munch of a range it does not meet (image B's rsegs). *)
Lemma cso_bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

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
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_state_online_e2_at in RE2. rewrite check_state_online_e1_at in RE1.
  (* the 4 bytes of M.e2_acked and of M.e1_us, as raw memory *)
  assert (L2 : length (TW.sub Bw TW.A_M_e2_acked 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_e2_acked, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_e2_acked, TW.OFF_M, TW.W_LEN. lia. }
  assert (L1 : length (TW.sub Bw TW.A_M_e1_us 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_e1_us, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_e1_us, TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 16 4 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF2.
  change (TB_M + 16) with 6155760 in BF2. change (TW.OFF_M + 16) with TW.A_M_e2_acked in BF2.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 20 4 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF1.
  change (TB_M + 20) with 6155764 in BF1. change (TW.OFF_M + 20) with TW.A_M_e1_us in BF1.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj (conj BF2 BF1) I) as BFC. clear BF2 BF1.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x85320-0x85324: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [[BF2 BF1] _].
  pose proof (cso_bytes_tp m m0 _ _ 6155760 (TW.sub Bw TW.A_M_e2_acked 4) MU1 ltac:(rewrite L2; lia) BF2) as BF2'.
  pose proof (cso_bytes_tp m m0 _ _ 6155764 (TW.sub Bw TW.A_M_e1_us 4) MU1 ltac:(rewrite L1; lia) BF1) as BF1'.
  clear BF2 BF1.
  assert (RD2 : ov_read_bytes rsegs m0 (wa 6155760) 4 = Some (TW.sub Bw TW.A_M_e2_acked 4)).
  { replace (wa 6155760) with (wa (6155760 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6155760 _ 0 4 BF2' ltac:(lia)) by (rewrite L2; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L2. lia. }
  clear BF2'.
  (* 0x85328-0x85330: a0 = 0x5dede0; a1 = M.e2_acked *)
  step. step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_e2_acked) with (TW.M_e2_acked Bw).
  clear RD2.
  (* 0x85334: beqz a1; the branch to the trap path needs M.e2_acked = 0 *)
  step.
  if_cases K2; [exfalso; zify_cond K2; first [ lia | (Z.div_mod_to_equations; lia) ] |].
  assert (RD1 : ov_read_bytes rsegs m0 (wa 6155764) 4 = Some (TW.sub Bw TW.A_M_e1_us 4)).
  { replace (wa 6155764) with (wa (6155764 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6155764 _ 0 4 BF1' ltac:(lia)) by (rewrite L1; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L1. lia. }
  clear BF1'.
  (* 0x85338: a0 = M.e1_us *)
  step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_e1_us) with (TW.M_e1_us Bw).
  clear RD1.
  (* 0x8533c: beqz a0; the branch to the trap path needs M.e1_us = 0 *)
  step.
  if_cases K1; [exfalso; zify_cond K1; first [ lia | (Z.div_mod_to_equations; lia) ] |].
  (* 0x85340-0x85348: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU1|].
  split; [match goal with WM' : wmono rsegs m m0 |- _ => exact WM' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

Print Assumptions check_state_online_holds_F.
