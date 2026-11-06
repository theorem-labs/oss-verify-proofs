(* check_inflight_new, entry 0x15154 (17 instructions):
     0x15154 addi sp,sp,-16 ; 0x15158 sd ra,8(sp)
     0x1515c auipc a0 ; 0x15160 addi a0 = &M (W_BASE_PLAIN)
     0x15164 lw a1,12(a0) (M.state) ; 0x15168 li a2,2 ; 0x1516c bne a1,a2 -> abort
     0x15170 lw a1,96(a0) (M.fly.on) ; 0x15174 bnez a1 -> abort
     0x15178 auipc a1 ; 0x1517c ld a1 (g_now) ; 0x15180 ld a0,56(a0) (M.backoff_until) ; 0x15184 bltu a1,a0 -> abort
     0x15188 ld ra,8(sp) ; 0x1518c addi sp,sp,16 ; 0x15190 ret
     0x15194 jal abort
   The model premise check_inflight_new_m B = Some (B', tt) gives M.state = ONLINE, M.fly.on = 0 and
   g_now >= M.backoff_until, so each of the three branches to 0x15194 falls through and abort is never reached. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem check_inflight_new_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_inflight_new_holds : check_inflight_new_contract.
Proof.
  unfold check_inflight_new_contract, check_inflight_new_ENTRY, check_inflight_new_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    WM HM Hal ST LO WO MI.
  (* the model: M.state = ONLINE, M.fly.on = 0, g_now >= M.backoff_until, and the world is returned unchanged *)
  unfold check_inflight_new_m in HM.
  destruct (negb (M_state B =? S_ONLINE) || truth (M_fly_on B)) eqn:C1; [discriminate HM|].
  destruct (g_now B <? M_backoff_until B) eqn:C2; [discriminate HM|].
  injection HM as HB. subst B'.
  apply orb_false_iff in C1 as [C1 C3].
  apply negb_false_iff, Z.eqb_eq in C1.
  unfold truth in C3. apply negb_false_iff, Z.eqb_eq in C3.
  assert (E1 : s32_at B 12 = 2) by exact C1.
  assert (E2 : s32_at B 96 = 0) by exact C3.
  assert (E3 : (u_at B 65000 8 <? u_at B 56 8) = false) by exact C2.
  assert (R1 : 0 <= u_at B 65000 8 < 2 ^ 64) by exact (u_at_range B 65000 8).
  assert (R2 : 0 <= u_at B 56 8 < 2 ^ 64) by exact (u_at_range B 56 8).
  clear C1 C2 C3.
  unfold w_off_stack in WO.
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (u64_range sp) as Rsp.
  carve_frame 16%nat ST.
  step.                                   (* addi sp,sp,-16 *)
  step.                                   (* sd ra,8(sp) *)
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
  step.                                   (* ld a0,56(a0): M.backoff_until *)
  step.                                   (* bltu a1,a0: g_now >= M.backoff_until, falls through *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; rewrite bv_ltu_Z, !unsigned_lit by lia; exact E3]
  end.
  step.                                   (* ld ra,8(sp) *)
  release_frame FR ST (bv_unsigned sp).
  step.                                   (* addi sp,sp,16 *)
  step.                                   (* ret *)
  apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj eq_refl _))))).
  all: eassumption.
Qed.
