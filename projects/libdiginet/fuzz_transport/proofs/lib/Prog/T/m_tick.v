(* The walk of m_tick in the plain image, against m_tick_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract m_lost_c m_tick_c.
Import ListNotations.
Open Scope Z_scope.

(* m_tick, 0x14d28-0x14d9c (fuzz/fuzz_transport.c:246-252): no prologue. a1 = M.state (lw 12(M)); state 2 (ONLINE)
   jumps to 0x14d70, state 1 (WAKING) falls to 0x14d44, any other state returns (bne to the ret at 0x14d94). Each
   timed arm computes g_now - <stamp> (sub) and <cfg ms field> * 1000 (lwu, mul) and compares them unsigned
   (WAKING: bltu to the ret, ONLINE: bgeu to the m_lost arm). The m_lost arms tail jump to m_lost (0x158ac) with
   a0 = 6 (R_WAKE_TIMEOUT, 0x14d68-0x14d6c) or 4 (R_SILENCE, 0x14d98-0x14d9c) and ra untouched, so m_lost returns to
   m_tick's caller. Every load is a world load (M at W_BASE_PLAIN; g_now and g_cfg through &g_fail_next = 0x42558). *)

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

Theorem m_tick_holds : m_lost_contract -> m_tick_contract.
Proof.
  intros ML. unfold m_tick_contract, m_tick_FRAME, m_tick_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' SPA ST LO WOS MI WM HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the ret at 0x14d94: memory and world unchanged *)
  assert (RET : forall a0' a1' a2' : word, B' = B ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14d94) fc None m (seg_rom rsegs))).
  { intros a0' a1' a2' EB. subst B'. step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* the tail jumps to m_lost: its post at m_tick's ra is m_tick's (both frames 0) *)
  assert (LOST : forall (why : Z) (a1' a2' : word), -2^31 <= why < 2^31 -> m_lost_m B why = Some (B', tt) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 why) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 m_lost_ENTRY) fc None m (seg_rom rsegs))).
  { intros why a1' a2' Hw HL. eapply evt_mono.
    - apply (ML ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 why) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m lo B B' why eq_refl Hw SPA ST LO WOS MI WM HL).
    - intros ms' P. unfold QQ. exact P. }
  unfold m_tick_m, S_WAKING, S_ONLINE in HM.
  pose proof (s32_range B 12) as RS.
  step. step. step. step. step.                    (* 0x14d28-0x14d38: a1 = M.state; beq a1, 2 *)
  if_cases K; rewrite mt_beq in K by (first [exact RS | lia]).
  - (* M.state = S_ONLINE *)
    apply Z.eqb_eq in K. change (s32_at B 12) with (M_state B) in K.
    replace (M_state B =? 1) with false in HM by (symmetry; apply Z.eqb_neq; lia).
    replace (M_state B =? 2) with true in HM by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota delta [andb] in HM.
    do 9 step.                                     (* 0x14d70-0x14d90: last_rx, g_now, offline_ms; bgeu *)
    if_cases K2; rewrite mt_ltu in K2 by (apply mt_u_at; lia); rewrite Bool.negb_involutive in K2;
      change (u_at B 65064 4) with (Cfg_offline_ms B) in K2;
      change (u_at B 65000 8) with (g_now B) in K2;
      change (u_at B 32 8) with (M_last_rx B) in K2;
      rewrite K2 in HM; cbv beta iota in HM.
    + (* elapsed >= ms(offline_ms): m_lost(R_SILENCE) *)
      step. step.                                  (* 0x14d98 li a0, 4; 0x14d9c j m_lost *)
      apply (LOST 4); [lia | exact HM].
    + injection HM as EB. apply (RET _ _ _ (eq_sym EB)).
  - apply Z.eqb_neq in K. change (s32_at B 12) with (M_state B) in K.
    step. step.                                    (* 0x14d3c li a2, 1; 0x14d40 bne a1, a2 *)
    if_cases K3; rewrite mt_beq in K3 by (first [exact RS | lia]);
      [apply Bool.negb_true_iff in K3; apply Z.eqb_neq in K3 | apply Bool.negb_false_iff in K3; apply Z.eqb_eq in K3];
      change (s32_at B 12) with (M_state B) in K3.
    + (* neither WAKING nor ONLINE: nothing *)
      replace (M_state B =? 1) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      replace (M_state B =? 2) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota delta [andb] in HM.
      injection HM as EB. apply (RET _ _ _ (eq_sym EB)).
    + (* M.state = S_WAKING *)
      replace (M_state B =? 1) with true in HM by (symmetry; apply Z.eqb_eq; lia).
      replace (M_state B =? 2) with false in HM by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota delta [andb] in HM.
      do 9 step.                                   (* 0x14d44-0x14d64: wake_sent, g_now, wake_timeout_ms; bltu *)
      if_cases K4; rewrite mt_ltu in K4 by (apply mt_u_at; lia);
        [apply Bool.negb_true_iff in K4 | apply Bool.negb_false_iff in K4];
        change (u_at B 65068 4) with (Cfg_wake_timeout_ms B) in K4;
        change (u_at B 65000 8) with (g_now B) in K4;
        change (u_at B 40 8) with (M_wake_sent B) in K4;
        rewrite K4 in HM; cbv beta iota in HM.
      * injection HM as EB. apply (RET _ _ _ (eq_sym EB)).
      * (* elapsed >= ms(wake_timeout_ms): m_lost(R_WAKE_TIMEOUT) *)
        step. step.                                (* 0x14d68 li a0, 6; 0x14d6c j m_lost *)
        apply (LOST 6); [lia | exact HM].
Qed.
