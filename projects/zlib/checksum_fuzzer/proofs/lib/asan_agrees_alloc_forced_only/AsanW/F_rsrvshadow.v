(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg AProto ABase ABytes AKit AKit2 RT_stubs F_ammap FsKit F_sysconf30 F_mmapfnr F_apoison APoisonR_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
End CANSEC1.
Notation RSRV_STACK := 592 (only parsing).

Section CANSEC2. Context {rc : runConstT}.


Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f7000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.


End CANSEC2.
