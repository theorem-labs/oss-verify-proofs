(* check_state_wake_code (fuzz/fuzz_transport.c:517-525), entry 0x14fec:
     0x14fec bne  a0, a1, 0x14ff4     rc <> want: the abort path
     0x14ff0 ret
     0x14ff4 addi sp, sp, -16; sd ra, 8(sp); jal abort; unimp
   The model premise check_state_wake_code_m B rc want = Some (B', tt) gives rc = want and B' = B, so the branch
   falls through to the ret and the abort path is never reached: no callee contract is needed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem check_state_wake_code_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_state_wake_code_holds : check_state_wake_code_contract.
Proof.
  unfold check_state_wake_code_contract, check_state_wake_code_ENTRY, check_state_wake_code_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' rc want -> -> Hrc Hwant WM HM SPA ST LO WOS MI.
  unfold check_state_wake_code_m in HM.
  destruct (Z.eqb_spec rc want) as [E|E]; cbn [negb] in HM; [|discriminate HM].
  injection HM as HB. subst want B'.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  step.                                   (* bne a0, a1: rc = want, falls through *)
  if_false.
  step.                                   (* ret *)
  apply evt_done. do 16 eexists. split; [reflexivity|].
  exact (conj MU (conj WMO (conj MI (conj ST (conj eq_refl WM))))).
Qed.
