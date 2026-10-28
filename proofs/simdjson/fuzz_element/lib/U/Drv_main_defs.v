(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import InitMem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Startup Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_aex.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0xbfa0c.
Definition RP1 : Z := 0x3bba8.
Definition RUSAGE : Z := 0x3bd10.
Definition RSTDERR_GOT : Z := 0xdc2f0.

End WithCeiling0.
Notation RSTAGE := 0xdda99%Z (only parsing).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 8388608.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells usegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  Definition ESTAT (mm : mem) : Prop :=
    rw_cells usegs mm 0xef4c0 [C8 (wz 0xef4c0); C8 (wz 0xef4c0); C8 (wz 0xef4c0); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells usegs mm 0x10f7f0 [C4 (wz 0)]
    /\ rw_cells usegs mm 0xdc450 [C8 (wz 0xd6820); C8 (wz 0xd6818)]
    /\ rw_cells usegs mm 0xd6818 [C8 (wz 0x3bae8)]
    /\ rw_cells usegs mm 0xdda98 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0xdc2d8 [C8 (wz 0xbfe74); C8 (wz 0)]
    /\ rw_cells usegs mm 0x10fd60 [C8 (wz 0)]
    /\ rw_cells usegs mm 0x10fd50 [C8 (wz 0)]
    /\ rw_cells usegs mm 0xdda28 [C8 (wz RSTDOUT)]
    /\ rw_cells usegs mm 0xdd938 [C8 (wz RSTDERR)]
    /\ rw_cells usegs mm RGOT_LLVMINIT [C8 (wz 0)]
    /\ rw_cells usegs mm 0xdd478 [C8 (wz 0xdd478)]
    /\ aex_inv mm.

  Definition estat_addr (a : Z) : Prop :=
    (0xef4c0 <= a < 0xef4e4) \/ (0x10f7f0 <= a < 0x10f7f8) \/ (0xdc450 <= a < 0xdc450 + 16) \/ (0xd6818 <= a < 0xd6820)
    \/ (0xdda98 <= a < 0xdda99) \/ (0xdc2d8 <= a < 0xdc2f0) \/ (0x10fd60 <= a < 0x10fd68) \/ (0x10fd50 <= a < 0x10fd58)
    \/ (0xdda28 <= a < 0xdda30) \/ (0xdd938 <= a < 0xdd940) \/ (0xdc2f8 <= a < 0xdc330)
    \/ (0xdd478 <= a < 0xdd480) \/ aex_addr a.

  Definition BASE (mm : mem) : Prop :=
    stk usegs mm LO (usp0 + -128) /\ mem_inv usegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    /\ bytes_at usegs mm usp0 (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
      ms = MS (mkR (wz RMAIN_RET) (wz (usp0 + -128)) (wz 0x10800) (wz RATP) t0 t1 t2
                   (wz 2) (wz 2) (wz 2) (wz (usp0 + 8)) (wz (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (wz RMAIN) (wz (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (wz RP1) (Z_to_bv 32 0) None mm (seg_rom usegs)
      /\ MFRAME mm pad s7 s6 s5 s4 /\ BASE mm
      /\ RHEAP (ps_init (reservedZ usegs)) [] mm
      /\ rw_cells usegs mm (errno_addr (wz RATP)) [C4 (wz 0)]
      /\ stdout_file mm stdout_init /\ stderr_wfile0 mm
      /\ (exists fl, sj_statics mm fl)
      /\ rw_cells usegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)]
      /\ stk usegs mm RSTAGE (RSTAGE + 65536).
End CTX.

Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt usegs (P1 sp0 argv envp uid TID) ms.

Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM usegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ usegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
