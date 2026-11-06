(* check_keepalive_due, entry 0x156c4 (18 instructions):
     0x156c4 auipc a0 ; 0x156c8 addi a0 = &M (W_BASE_UBSAN)
     0x156cc lw a1,12(a0) (M.state) ; 0x156d0 li a2,2 ; 0x156d4 bne a1,a2 -> abort
     0x156d8 lw a1,96(a0) (M.fly.on) ; 0x156dc bnez a1 -> abort
     0x156e0 auipc a1 ; 0x156e4 ld a1 (g_now) ; 0x156e8 ld a2,56(a0) (M.backoff_until) ; 0x156ec bltu a1,a2 -> abort
     0x156f0 ld a0,48(a0) (M.next_ka) ; 0x156f4 bltu a1,a0 -> abort
     0x156f8 ret
     0x156fc addi sp,sp,-16 ; 0x15700 sd ra,8(sp) ; 0x15704 jal abort ; 0x15708 unimp
   The model premise check_keepalive_due_m B = Some (B', tt) gives M.state = ONLINE, M.fly.on = 0,
   g_now >= M.backoff_until and g_now >= M.next_ka, so each of the four branches to 0x156fc falls through and abort
   is never reached; the path that returns touches neither the stack nor memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem check_keepalive_due_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_keepalive_due_holds : check_keepalive_due_contract.
Proof.
  unfold check_keepalive_due_contract, check_keepalive_due_ENTRY, check_keepalive_due_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    WM HM Hal ST LO WO MI.
  (* the model: M.state = ONLINE, M.fly.on = 0, g_now >= M.backoff_until, g_now >= M.next_ka, and the world is
     returned unchanged *)
  unfold check_keepalive_due_m in HM.
  destruct (negb (M_state B =? S_ONLINE) || truth (M_fly_on B) || (g_now B <? M_backoff_until B)
            || (g_now B <? M_next_ka B)) eqn:C1; [discriminate HM|].
  injection HM as HB. subst B'.
  apply orb_false_iff in C1 as [C1 C4].
  apply orb_false_iff in C1 as [C1 C3].
  apply orb_false_iff in C1 as [C1 C2].
  apply negb_false_iff, Z.eqb_eq in C1.
  unfold truth in C2. apply negb_false_iff, Z.eqb_eq in C2.
  assert (E1 : s32_at B 12 = 2) by exact C1.
  assert (E2 : s32_at B 96 = 0) by exact C2.
  assert (E3 : (u_at B 65000 8 <? u_at B 56 8) = false) by exact C3.
  assert (E4 : (u_at B 65000 8 <? u_at B 48 8) = false) by exact C4.
  assert (R1 : 0 <= u_at B 65000 8 < 2 ^ 64) by exact (u_at_range B 65000 8).
  assert (R2 : 0 <= u_at B 56 8 < 2 ^ 64) by exact (u_at_range B 56 8).
  assert (R3 : 0 <= u_at B 48 8 < 2 ^ 64) by exact (u_at_range B 48 8).
  clear C1 C2 C3 C4.
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  step.                                   (* auipc a0 *)
  step.                                   (* addi a0: &M *)
  step.                                   (* lw a1,12(a0): M.state *)
  rewrite E1.
  step.                                   (* li a2,2 *)
  step.                                   (* bne a1,a2: M.state = ONLINE, falls through *)
  if_false.
  step.                                   (* lw a1,96(a0): M.fly.on *)
  rewrite E2.
  step.                                   (* bnez a1: M.fly.on = 0, falls through *)
  if_false.
  step.                                   (* auipc a1 *)
  step.                                   (* ld a1: g_now *)
  step.                                   (* ld a2,56(a0): M.backoff_until *)
  step.                                   (* bltu a1,a2: g_now >= M.backoff_until, falls through *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; rewrite bv_ltu_Z, !unsigned_lit by lia; exact E3]
  end.
  step.                                   (* ld a0,48(a0): M.next_ka *)
  step.                                   (* bltu a1,a0: g_now >= M.next_ka, falls through *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; rewrite bv_ltu_Z, !unsigned_lit by lia; exact E4]
  end.
  step.                                   (* ret *)
  apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj eq_refl _))))).
  all: eassumption.
Qed.
