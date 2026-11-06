(* WireCmRel: the release and return piece of the image-B walk of check_meter (fuzz_wire.asan-ubsan 0x8016c), the
   footprint run (lib/Lib/ExecF.v evtF) of lib/B/Prog/WireCmIface.v cm_rel_stmt, stepped by lib/Lib/StepF.v in the
   form of reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v cv_end_F (recipes commit 0295462466b2):
     0x803c4 `li a0, -8`, 0x803c8 `sb a0, 4(s7)`: ctr's shadow byte := 0xf8;
     0x803cc `lui`, 0x803d0 `addiw`, 0x803d4 `sd a0, 0(s6)`: the frame's first word := 0x45e0360e;
     0x803d8 `beqz s2` not taken (s2 = Fa >= 4096);
     0x803dc `li a0, -11`, 0x803e0 .. 0x803fc the eight `sb a0, k(s7)`: the frame's shadow bytes := 0xf5;
     0x80400 `ld a0, 56(s2)`: the flag pointer FL; 0x80404 `sb zero, 0(a0)`; 0x80408 `j`;
     0x8042c `addi sp, s0, -128`, 0x80430 .. 0x8045c the twelve reloads, 0x80460 `addi sp, sp, 128`, 0x80464 `ret`.
   Each store address is the base of a rw_cells premise (shadow_addr Fa, Fa, FL), so StepF's solve_store turns the
   store into a cell update; the separation premises give lia the disjointness that keeps the other cells. The
   reloads read the ro_cells of the twelve saved words, restated at sp0 + -96 (the form StepF folds the addresses
   of `addi sp, s0, -128` and `ld r, k(sp)` into). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Ltac cm_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: the proof first computes the closed name of its goal to its value. *)
Ltac cm_lit X := let v := eval vm_compute in X in change X with v.

Lemma cm_rel : cm_rel_stmt.
Proof.
  unfold cm_rel_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Fa FL sp0 sj hj lj cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    HFa HFsp HSD HSsp HFL0 HFLsp HFLa HFLs Hsp0 Es0 SH HD PF FLC FR RSH RHD RPF RFL RFR.
  cm_lit CM_REL.
  pose proof (rw_cells_bound _ _ _ _ SH) as BSH. cbn [cells_size csize Nat.add] in BSH.
  pose proof (ro_cells_bound _ _ _ _ PF) as BPF. cbn [cells_size csize Nat.add] in BPF.
  assert (UFa : bv_unsigned (Z_to_bv 64 Fa) = Fa) by (apply unsigned_lit; lia).
  assert (Es0' : s0 = Z_to_bv 64 sp0) by (apply bv_eq; rewrite Es0, unsigned_lit by lia; reflexivity).
  subst s0. clear Es0.
  replace (sp0 - 96) with (sp0 + -96) in FR, RFR by lia.
  pose proof (munch_refl [(shadow_addr Fa, shadow_addr Fa + 8); (Fa, Fa + 8); (FL, FL + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x803c4 `li a0, -8`; 0x803c8 `sb a0, 4(s7)` *)
  do 2 step.
  (* 0x803cc `lui`; 0x803d0 `addiw`; 0x803d4 `sd a0, 0(s6)` *)
  do 3 step.
  (* 0x803d8 `beqz s2` not taken *)
  step. if_false.
  (* 0x803dc `li a0, -11`; the eight shadow stores *)
  do 9 step.
  (* 0x80400 `ld a0, 56(s2)`; 0x80404 `sb zero, 0(a0)`; 0x80408 `j` *)
  do 3 step.
  (* 0x8042c `addi sp, s0, -128`; the twelve reloads; `addi sp, sp, 128`; `ret` *)
  do 15 step.
  cm_memF ltac:(fun mm => apply evtF_done; exists mm).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  match goal with H : rw_cells _ _ FL _ |- _ => destruct H as [[_ HBf] _] end.
  cbn [cells_bytes cbytes app] in HBf. exact HBf.
Qed.
