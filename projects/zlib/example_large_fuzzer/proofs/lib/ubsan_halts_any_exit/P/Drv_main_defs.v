(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Layout Exit InitMem Startup Printf_stdio_iface Zlib_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_large_fuzzer_repro.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Src_zlib_example_large_fuzzer_repro.M.phdrs.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x201b4.
Definition RP1 : Z := 0x159fc.
Definition RUSAGE : Z := 0x15b64.
Definition RSTDERR_GOT : Z := 0x293d8.
End WithCeiling0.
Notation RSTAGE := 0x2a699%Z (only parsing).


Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 6144513.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  Definition ESTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0x3a6e8 [C8 (wz 0x3a6e8); C8 (wz 0x3a6e8); C8 (wz 0x3a6e8); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells psegs mm 0x5aa10 [C4 (wz 0)]
    /\ rw_cells psegs mm 0x29428 [C8 (wz 0x29238); C8 (wz 0x29230)]
    /\ rw_cells psegs mm 0x29230 [C8 (wz 0x1593c)]
    /\ rw_cells psegs mm 0x2a698 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x293c8 [C8 (wz 0x20530); C8 (wz 0)]
    /\ rw_cells psegs mm 0x2a438 [C8 (wz 0x2a438)]
    /\ rw_cells psegs mm 0x5ae68 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x5ae58 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x2a638 [C8 (wz RSTDOUT)]
    /\ rw_cells psegs mm 0x2a548 [C8 (wz RSTDERR)]
    /\ rw_cells psegs mm RGOT_LLVMINIT [C8 (wz 0)].

  Definition estat_addr (a : Z) : Prop :=
    (0x3a6e8 <= a < 0x3a70c) \/ (0x5aa10 <= a < 0x5aa10 + 4) \/ (0x29428 <= a < 0x29428 + 16) \/ (0x29230 <= a < 0x29238)
    \/ (0x2a698 <= a < 0x2a699) \/ (0x293c8 <= a < 0x293d8) \/ (0x5ae68 <= a < 0x5ae70) \/ (0x5ae58 <= a < 0x5ae60)
    \/ (0x2a638 <= a < 0x2a640) \/ (0x2a548 <= a < 0x2a550) \/ (0x293e0 <= a < 0x293e0 + 8) \/ (0x2a438 <= a < 0x2a438 + 8).

  Definition BASE (mm : mem) : Prop :=
    stk psegs mm LO (usp0 + -128) /\ mem_inv psegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    (* the entry block is the family's img_at (727298f3's build_stack_bytes), the
       conjunct at_main states *)
    /\ bytes_at psegs mm usp0 (img_at sp0 argv envp uid).

  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
      ms = MS (mkR (wz RMAIN_RET) (wz (usp0 + -128)) (wz 0x10800) (wz RATP) t0 t1 t2
                   (wz 2) (wz 2) (wz 2) (wz (usp0 + 8)) (wz (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (wz RMAIN) (wz (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (wz RP1) (Z_to_bv 32 0) None mm (seg_rom psegs)
      /\ MFRAME mm pad s7 s6 s5 s4 /\ BASE mm
      /\ RHEAP (ps_init (reservedZ psegs)) [] mm
      /\ rw_cells psegs mm (errno_addr (wz RATP)) [C4 (wz 0)]
      /\ stdout_file mm stdout_init /\ stderr_wfile0 mm
      /\ zl_statics0 mm
      /\ rdrv_statics mm
      /\ stk psegs mm RSTAGE (RSTAGE + 65536).
End CTX.


Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt psegs (P1 sp0 argv envp uid TID) ms.

Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM psegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ psegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
