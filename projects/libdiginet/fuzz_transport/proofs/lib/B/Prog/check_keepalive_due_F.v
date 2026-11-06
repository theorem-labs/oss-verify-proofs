From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_keepalive_due_c check_keepalive_due_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_keepalive_due_contract_F (image B, entry 0x84868, frame 16 bytes), with StepF's step: each
   access side goal is closed from an rng fact for the accessed range. Form: image A's walk of this function
   (lib/A/Prog/check_keepalive_due_F.v) at image B's addresses, with image B's world kept by TWorldB.TMAP_B_kept (as
   the image-B walk lib/B/Prog/check_state_online_F.v).

   The walk (statement header check_keepalive_due_c.v:18-44):
     0x84868-0x8486c  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x84870-0x84874  auipc a0; addi a0: a0 = 0x5dede0 = TB_M, the base of M.
     0x84878          lw a1,12(a0): a1 = M.state, sign-extended.
     0x8487c-0x84880  li a2,2; bne a1,a2, 0x848b0.
     0x84884          lw a1,96(a0): a1 = M.fly.on, sign-extended.
     0x84888          bnez a1, 0x848b0.
     0x8488c-0x84890  auipc a1; ld a1: a1 = g_now (TB_g_now = 0x5ded80).
     0x84894          ld a2,56(a0): a2 = M.backoff_until.
     0x84898          bltu a1,a2, 0x848b0.
     0x8489c          ld a0,48(a0): a0 = M.next_ka.
     0x848a0          bltu a1,a0, 0x848b0.
     0x848a4-0x848ac  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x848b0 / 0x848b4 / 0x848b8 (__asan_handle_no_return, abort, then the unimp word 0xc0001073) is
   never reached: the model premise check_keepalive_due_m Bw = Some (Bw', tt) gives M_state Bw = 2, M_fly_on Bw = 0,
   g_now Bw >= M_backoff_until Bw, g_now Bw >= M_next_ka Bw and Bw' = Bw, so each of the four branches falls through;
   the unimp word follows the abort call on that path only, so the same facts rule it out. By the world relation the
   loaded bytes are sub Bw (OFF + k) n of the payload row the load hits (ckd_read), so the loaded values are
   Z_to_bv 64 of M_state Bw and M_fly_on Bw (lw_world) and of g_now Bw, M_backoff_until Bw and M_next_ka Bw (ld_world);
   the two bltu compare the unsigned values, which are the u_at values themselves (0 <= u_at < 2^64). The function has
   no UBSan check of its own, and the statement has no alignment or range premise.

   The world relation after the frame store: the store writes only the frame (munch), and the frame lies outside the
   hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise; TMAP_B_kept), so tw_at holds of
   the same Bw at the memory after it; the five loads read through that fact, and no later step writes. *)

(* A load of c bytes at b + k inside ONE payload row of TMAP_B reads sub Bw (o + k) c. *)
Lemma ckd_read : forall (m : word -> option byte) Bw o b n k (c : nat),
  tw_at TMAP_B (csw_view m) Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat c <= n ->
  ov_read_bytes rsegs m (wa (b + k)) c = Some (TW.sub Bw (o + k) c).
Proof.
  intros m Bw o b n k c HW Hin Hk Hkc.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (L : length (TW.sub Bw (o + k) c) = c).
  { apply TWorldLemmas.length_sub; [lia|]. rewrite (tw_len TMAP_B _ Bw HW). unfold TW.W_LEN in *. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw o b n k c TMAP_B_ok HW Hin Hk Hkc) as BF.
  pose proof (bytes_at_read rsegs m (b + k) _ 0 c BF ltac:(lia) ltac:(rewrite L; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R.
  cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* A branch that falls through by H : c = false. StepF's if_false_by does not fit here: with H in context, replace
   closes the equality c = false itself (it is an assumption) and leaves one goal, not the two if_false_by expects. *)
Ltac ckd_if_false H :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; try (symmetry; exact H); cbv iota
  end.

Theorem check_keepalive_due_holds_F : check_keepalive_due_contract_F.
Proof.
  unfold check_keepalive_due_contract_F, CHECK_KEEPALIVE_DUE, CHECK_KEEPALIVE_DUE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RST RFL RNW RBO RNK.
  (* the model: M.state = S_ONLINE, M.fly.on = 0, M.backoff_until <= g_now, M.next_ka <= g_now, and Bw' = Bw *)
  assert (HF : TW.M_state Bw = 2 /\ TW.M_fly_on Bw = 0 /\ (TW.g_now Bw <? TW.M_backoff_until Bw) = false /\
               (TW.g_now Bw <? TW.M_next_ka Bw) = false /\ Bw' = Bw).
  { unfold TC.check_keepalive_due_m, TC.truth, TC.S_ONLINE in HM.
    destruct (Z.eqb_spec (TW.M_state Bw) 2) as [ES|ES]; cbn [negb orb] in HM; [|discriminate HM].
    destruct (Z.eqb_spec (TW.M_fly_on Bw) 0) as [EF|EF]; cbn [negb orb] in HM; [|discriminate HM].
    destruct (TW.g_now Bw <? TW.M_backoff_until Bw) eqn:EB; cbn [negb orb] in HM; [discriminate HM|].
    destruct (TW.g_now Bw <? TW.M_next_ka Bw) eqn:EN; cbn [negb orb] in HM; [discriminate HM|].
    split; [exact ES|]. split; [exact EF|]. split; [reflexivity|]. split; [reflexivity|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as (HS & HFL & HBO & HNK & ->). clear HM.
  (* the unsigned values of the three 8-byte words, for the two bltu *)
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8) as RVN.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_backoff_until 8) as RVB.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_next_ka 8) as RVK.
  change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw) in RVN.
  change (TW.u_at Bw TW.A_M_backoff_until 8) with (TW.M_backoff_until Bw) in RVB.
  change (TW.u_at Bw TW.A_M_next_ka 8) with (TW.M_next_ka Bw) in RVK.
  change (8 * Z.of_nat 8) with 64 in RVN, RVB, RVK.
  assert (CBO : bv_ltu (Z_to_bv 64 (TW.g_now Bw)) (Z_to_bv 64 (TW.M_backoff_until Bw)) = false).
  { rewrite bv_ltu_Z, !unsigned_lit by lia. exact HBO. }
  assert (CNK : bv_ltu (Z_to_bv 64 (TW.g_now Bw)) (Z_to_bv 64 (TW.M_next_ka Bw)) = false).
  { rewrite bv_ltu_Z, !unsigned_lit by lia. exact HNK. }
  clear HBO HNK RVN RVB RVK.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_keepalive_due_state_at in RST.
  rewrite check_keepalive_due_fly_on_at in RFL.
  rewrite check_keepalive_due_now_at in RNW.
  rewrite check_keepalive_due_backoff_at in RBO.
  rewrite check_keepalive_due_next_ka_at in RNK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x84868-0x8486c: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the world relation at the memory after the frame store: same world *)
  pose proof (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1
    ltac:(unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia)) as HW0.
  (* 0x84870-0x84874: a0 = TB_M *)
  step. step.
  (* 0x84878: a1 = M.state = 2 *)
  pose proof (ckd_read m0 Bw TW.OFF_M TB_M TW.SZ_M 12 4 HW0 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD.
  change (TB_M + 12) with 6155756 in RD. change (TW.OFF_M + 12) with TW.A_M_state in RD.
  step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw). rewrite HS.
  clear RD.
  (* 0x8487c-0x84880: li a2,2; bne a1,a2 falls through *)
  step. step. if_false.
  (* 0x84884: a1 = M.fly.on = 0 *)
  pose proof (ckd_read m0 Bw TW.OFF_M TB_M TW.SZ_M 96 4 HW0 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD.
  change (TB_M + 96) with 6155840 in RD. change (TW.OFF_M + 96) with TW.A_M_fly_on in RD.
  step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_fly_on) with (TW.M_fly_on Bw). rewrite HFL.
  clear RD.
  (* 0x84888: bnez a1 falls through *)
  step. if_false.
  (* 0x8488c-0x84890: a1 = g_now *)
  pose proof (ckd_read m0 Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 HW0 TMAP_B_g_now ltac:(lia)
    ltac:(unfold TW.SZ_g_now; lia)) as RD.
  change (TB_g_now + 0) with 6155648 in RD. change (TW.OFF_g_now + 0) with TW.OFF_g_now in RD.
  step. step.
  rewrite ld_world. change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw).
  clear RD.
  (* 0x84894: a2 = M.backoff_until *)
  pose proof (ckd_read m0 Bw TW.OFF_M TB_M TW.SZ_M 56 8 HW0 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD.
  change (TB_M + 56) with 6155800 in RD. change (TW.OFF_M + 56) with TW.A_M_backoff_until in RD.
  step.
  rewrite ld_world. change (TW.u_at Bw TW.A_M_backoff_until 8) with (TW.M_backoff_until Bw).
  clear RD.
  (* 0x84898: bltu a1,a2 falls through: g_now >= M.backoff_until *)
  step. ckd_if_false CBO.
  (* 0x8489c: a0 = M.next_ka *)
  pose proof (ckd_read m0 Bw TW.OFF_M TB_M TW.SZ_M 48 8 HW0 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD.
  change (TB_M + 48) with 6155792 in RD. change (TW.OFF_M + 48) with TW.A_M_next_ka in RD.
  step.
  rewrite ld_world. change (TW.u_at Bw TW.A_M_next_ka 8) with (TW.M_next_ka Bw).
  clear RD.
  (* 0x848a0: bltu a1,a0 falls through: g_now >= M.next_ka *)
  step. ckd_if_false CNK.
  (* 0x848a4-0x848ac: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU1|].
  split; [match goal with WM' : wmono rsegs m m0 |- _ => exact WM' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  exact HW0.
Qed.

Print Assumptions check_keepalive_due_holds_F.
