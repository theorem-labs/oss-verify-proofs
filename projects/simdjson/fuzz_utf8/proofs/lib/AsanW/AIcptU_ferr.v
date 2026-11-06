(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit MonadF I_fwrite F_fflushU AExitU_wr AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AIcptU_hmap AIcptU_fflush AIcptU_defs.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section Chains.
  Variables (T SLO SHI : Z).

  Theorem fflush_err_proof : fflush_err_stmt (icptU T) (icptU_rng T).
  Proof.
    unfold fflush_err_stmt. intros until guard. intros ST SEF [GS GU] IC MI -> -> LO GLO ALO SP16 RSTK RI [RBE RBO].
    pose proof IC as ((R1 & R2 & R3 & R4 & R5 & R6) & (M1 & M2 & B1 & B2 & TLO & THI & TAL)).
    unfold GLOBALS_TOP in GLO. unfold HMAP, BOFF_ERR, BOFF_OUT in *.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (T + 2586600, T + 2586600 + 8)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (fun m' H' => rw_cells_same_bytes m m' (T + 2586600) hm_bucket0 B1 H' ltac:(lia)) as SAME.
    unfold FFLUSH_STUB. unfold hm_bucket0 in B1, B2. unfold file_cells in EFC. unfold got_ssp, ssp_guard in GS, GU.
    (* [comment removed for export] *)
    call (fflush_i_pre RNG). all: iprem.
    replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
    (* [comment removed for export] *)
    call_sp (fflush_stderr_spec RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- stderr_file _ => exists eflags, emode, ee, ewend, etail; unfold file_cells; eassumption
         | |- @eq word _ _ => reflexivity
         | |- _ => iprem
         end.
    destruct POST0 as (eflags' & emode' & ee' & ewend' & etail' & EFC'). unfold file_cells in EFC'.
    (* [comment removed for export] *)
    eapply evtF_cut; [eapply (fflush_i_post RNG) with (lo := lo) (T := T) (addr := 0x16a8e8) (boff := 2586600)|].
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- _ \/ _ => right; split; reflexivity
         | |- rw_cells _ _ _ hm_bucket0 => unfold hm_bucket0; eassumption
         | |- rw_cells _ _ _ _ => unfold HMAP; first [eassumption | (replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; eassumption)]
         | |- stk _ _ _ _ => replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; eassumption
         | |- _ => unfold KHIGH in *; atop_facts; iprem
         end.
    lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
    apply evtF_done. unfold icpt_post.
    do 15 eexists. split; [reflexivity|].
    split. { eapply (munch_drop_eq [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z (T + 2586600) 8); [exact MU|].
             intros xx Hx _. apply (SAME _ POST0). unfold hm_bucket0. cbn [cells_size csize Nat.add]. lia. }
    split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split. { unfold ssp_cells, got_ssp, ssp_guard. split; assumption. }
    split. { unfold icptU, icpt_rt, icpt_tab, HMAP, BOFF_ERR, BOFF_OUT. unfold hm_bucket0 in POST0 |- *.
             repeat match goal with |- _ /\ _ => split end; assumption. }
    exists eflags', emode', ee', ewend', etail'. unfold file_cells. exact EFC'.
  Qed.
End Chains.
End CANSEC1.
