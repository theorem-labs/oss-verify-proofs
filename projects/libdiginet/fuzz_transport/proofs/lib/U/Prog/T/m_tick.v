(* The walk of m_tick in the ubsan image, against m_tick_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract m_set_c m_tick_c.
Import ListNotations.
Open Scope Z_scope.

(* m_tick, 0x14e8c-0x14f0c (fuzz/fuzz_transport.c:246-252, m_lost inlined): no prologue. a0 = &M = W_BASE_UBSAN
   throughout, a1 = M.state (lw 12(M)); state 2 (ONLINE) jumps to 0x14ed4, state 1 (WAKING) falls to 0x14ea8, any
   other state returns (bne to the ret at 0x14ef8). Each timed arm computes g_now - <stamp> (sub) and
   <cfg ms field> * 1000 (lwu, mul) and compares them unsigned (WAKING: bltu to the ret, ONLINE: bgeu to the lost arm).
   The lost arm (a1 = 6, R_WAKE_TIMEOUT, from 0x14ecc; a1 = 4, R_SILENCE, from 0x14efc) is m_lost inlined:
   M.desk_counter_valid = 0 (sw 76(M), 0x14f00), M.fly.on = 0 (sw 96(M), 0x14f04), a0 = S_IDLE, then a tail jump to
   m_set (0x15e3c) with ra untouched, so m_set returns to m_tick's caller. Every load and store is in the world (M at
   W_BASE_UBSAN; g_now and g_cfg through &g_fail_next = 0x430c8). *)

(* beq / bne on a sign-extended 32-bit load against a small literal *)
Lemma mt_beq : forall x c, -2^31 <= x < 2^31 -> 0 <= c < 2^31 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 c) = (x =? c).
Proof.
  intros x c Hx Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small c) by lia.
  destruct (Z_le_gt_dec 0 x) as [P|N].
  - rewrite (Z.mod_small x) by lia. reflexivity.
  - rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.eqb_spec (x + 1 * 2^64) c); destruct (Z.eqb_spec x c); lia.
Qed.

(* the timed arms' bltu / bgeu: (uint64_t)(now - stamp) against ms(v) = (uint64_t)v * 1000 *)
Lemma mt_ltu : forall now t v, 0 <= now < 2^64 -> 0 <= t < 2^64 -> 0 <= v < 2^64 ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 now) - bv_unsigned (Z_to_bv 64 t)))
         (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) * 1000))
  = negb (h_ms_m v <=? u64 (now - t)).
Proof.
  intros now t v Hn Ht Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small now), (Z.mod_small t), (Z.mod_small v) by lia.
  unfold h_ms_m, u64. apply Z.ltb_antisym.
Qed.

Lemma mt_u_at : forall bs k n, (n <= 8)%nat -> 0 <= u_at bs k n < 2^64.
Proof.
  intros bs k n Hn. pose proof (u_at_range bs k n) as R.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(* the inlined m_lost writes M.desk_counter_valid then M.fly.on; the model writes them in the other order *)
Lemma mt_lost_world : forall B, length B = Z.to_nat W_LEN ->
  upd (upd B 76 (put 4 0)) 96 (put 4 0) = set_M_desk_counter_valid (set_M_fly_on B 0) 0.
Proof.
  intros B LB.
  change (upd (upd B 76 (put 4 0)) 96 (put 4 0) = upd (upd B 96 (put 4 0)) 76 (put 4 0)).
  assert (LP : length (put 4 0) = 4%nat) by reflexivity.
  assert (LBz : Z.of_nat (length B) = 65616) by (rewrite LB, Z2Nat.id by (unfold W_LEN; lia); reflexivity).
  apply upd_upd_comm; rewrite ?LP, ?LBz; lia.
Qed.

Theorem m_tick_holds : m_set_contract -> m_tick_contract.
Proof.
  intros MSC. unfold m_tick_contract, m_tick_FRAME, m_tick_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' SPA ST LO WOS MI WM HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the ret at 0x14ef8: memory and world unchanged *)
  assert (RET : forall a0' a1' a2' a3' : word, B' = B ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14ef8) fc None m (seg_rom rsegs))).
  { intros a0' a1' a2' a3' EB. subst B'. step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* the inlined m_lost at 0x14f00 (a0 = &M, a1 = why): two world stores, then the tail jump to m_set, whose post at
     m_tick's ra is m_tick's once the stores' footprint is composed with m_set's (both frames 0) *)
  assert (LOST : forall (why : Z) (a2' a3' : word), -2^31 <= why < 2^31 -> m_lost_m B why = Some (B', tt) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x33300) (Z_to_bv 64 why) a2' a3' a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14f00) fc None m (seg_rom rsegs))).
  { intros why a2' a3' Hw HL. unfold m_lost_m, S_IDLE in HL.
    pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB.
    pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
    pose proof (wmono_refl rsegs m) as WMo.
    step.                                          (* 0x14f00 sw zero, 76(a0): M.desk_counter_valid = 0 *)
    step.                                          (* 0x14f04 sw zero, 96(a0): M.fly.on = 0 *)
    step.                                          (* 0x14f08 li a0, 0 *)
    step.                                          (* 0x14f0c j m_set *)
    lazymatch goal with
    | H : rw_cells rsegs ?m2 W_BASE_UBSAN [CB (Z.to_nat W_LEN) ?B2] |- _ =>
        replace B2 with (set_M_desk_counter_valid (set_M_fly_on B 0) 0) in H
          by (symmetry; apply mt_lost_world; exact LB);
        rename H into WM2
    end.
    eapply evt_mono.
    - eapply (MSC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 why) a2' a3' a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ lo _ B' 0 why eq_refl eq_refl);
        [ lia | exact Hw | exact SPA | eassumption | exact LO | exact WOS | eassumption | exact WM2 | exact HL ].
    - intros ms' (t0' & t1' & t2' & a0' & a1' & a2'' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU' & WM' & MI' & ST' & WW').
      unfold QQ. exists t0', t1', t2', a0', a1', a2'', a3'', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [exact E|].
      split; [eapply munch_trans; [ | exact MU' ]; eassumption|].
      split; [eapply wmono_trans; [ | exact WM' ]; eassumption|].
      split; [exact MI'|]. split; [exact ST'|exact WW']. }
  unfold m_tick_m, S_WAKING, S_ONLINE in HM.
  pose proof (s32_range B 12) as RS.
  step. step. step. step. step.                    (* 0x14e8c-0x14e9c: a1 = M.state; beq a1, 2 *)
  if_cases K; rewrite mt_beq in K by (first [exact RS | lia]).
  - (* M.state = S_ONLINE *)
    apply Z.eqb_eq in K. change (s32_at B 12) with (M_state B) in K.
    replace (M_state B =? 1) with false in HM by (symmetry; apply Z.eqb_neq; lia).
    replace (M_state B =? 2) with true in HM by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota delta [andb] in HM.
    do 9 step.                                     (* 0x14ed4-0x14ef4: last_rx, g_now, offline_ms; bgeu *)
    if_cases K2; rewrite mt_ltu in K2 by (apply mt_u_at; lia); rewrite Bool.negb_involutive in K2;
      change (u_at B 65064 4) with (Cfg_offline_ms B) in K2;
      change (u_at B 65000 8) with (g_now B) in K2;
      change (u_at B 32 8) with (M_last_rx B) in K2;
      rewrite K2 in HM; cbv beta iota in HM.
    + (* elapsed >= ms(offline_ms): m_lost(R_SILENCE) *)
      step.                                        (* 0x14efc li a1, 4 *)
      apply (LOST 4); [lia | exact HM].
    + injection HM as EB. apply (RET _ _ _ _ (eq_sym EB)).
  - apply Z.eqb_neq in K. change (s32_at B 12) with (M_state B) in K.
    step. step.                                    (* 0x14ea0 li a2, 1; 0x14ea4 bne a1, a2 *)
    if_cases K3; rewrite mt_beq in K3 by (first [exact RS | lia]);
      [apply Bool.negb_true_iff in K3; apply Z.eqb_neq in K3 | apply Bool.negb_false_iff in K3; apply Z.eqb_eq in K3];
      change (s32_at B 12) with (M_state B) in K3.
    + (* neither WAKING nor ONLINE: nothing *)
      replace (M_state B =? 1) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      replace (M_state B =? 2) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota delta [andb] in HM.
      injection HM as EB. apply (RET _ _ _ _ (eq_sym EB)).
    + (* M.state = S_WAKING *)
      replace (M_state B =? 1) with true in HM by (symmetry; apply Z.eqb_eq; lia).
      replace (M_state B =? 2) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota delta [andb] in HM.
      do 9 step.                                   (* 0x14ea8-0x14ec8: wake_sent, g_now, wake_timeout_ms; bltu *)
      if_cases K4; rewrite mt_ltu in K4 by (apply mt_u_at; lia);
        [apply Bool.negb_true_iff in K4 | apply Bool.negb_false_iff in K4];
        change (u_at B 65068 4) with (Cfg_wake_timeout_ms B) in K4;
        change (u_at B 65000 8) with (g_now B) in K4;
        change (u_at B 40 8) with (M_wake_sent B) in K4;
        rewrite K4 in HM; cbv beta iota in HM.
      * injection HM as EB. apply (RET _ _ _ _ (eq_sym EB)).
      * (* elapsed >= ms(wake_timeout_ms): m_lost(R_WAKE_TIMEOUT) *)
        step. step.                                (* 0x14ecc li a1, 6; 0x14ed0 j 0x14f00 *)
        apply (LOST 6); [lia | exact HM].
Qed.
