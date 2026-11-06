From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib.
Import ListNotations.
Open Scope Z_scope.

Definition FREE_PC : Z := 0x171f0.
Definition R29_RET : Z := 0x1445c.

Lemma slot_R29_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 R29_RET) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 FREE_PC) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold EXIT, FREE_PC, R29_RET.
  step. step.
  apply evt_done. reflexivity.
Qed.

Lemma slot_R29_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
  sp = Z_to_bv 64 X -> 0 <= X -> X + 2592 <= 2 ^ 64 ->
  rw_cells rsegs m (X + 2488) (saved_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra) ->
  evt rsegs
    (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 (X + 2592)) gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                         F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R29_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra Esp HX0 HX1 SV.
  subst sp. unfold R29_RET, saved_cells in *.
  step. step.
  replace (X + 560 + 2024) with (X + 2488 + 96) by lia.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step.
  apply evt_done. reflexivity.
Qed.
