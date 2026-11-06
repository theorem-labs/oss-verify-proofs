(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit InitMem Startup Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_aex.
From OSSVerify.simdjson.fuzz_element.images Require Import Plain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Plain.M.phdrs.

From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0xb3e0c.
Definition RP1 : Z := 0x3b708.
Definition RUSAGE : Z := 0x3b870.
Definition RSTDERR_GOT : Z := 0xd06f0.

End WithCeiling0.
Notation RSTAGE := 0xd1b99%Z (only parsing).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 8388608.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  Definition ESTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0xe35c0 [C8 (wz 0xe35c0); C8 (wz 0xe35c0); C8 (wz 0xe35c0); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells psegs mm 0x1038f0 [C4 (wz 0)]
    /\ rw_cells psegs mm 0xd0850 [C8 (wz 0xcac20); C8 (wz 0xcac18)]
    /\ rw_cells psegs mm 0xcac18 [C8 (wz 0x3b648)]
    /\ rw_cells psegs mm 0xd1b98 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0xd06d8 [C8 (wz 0xb4274); C8 (wz 0)]
    /\ rw_cells psegs mm 0x103e60 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x103e50 [C8 (wz 0)]
    /\ rw_cells psegs mm 0xd1b28 [C8 (wz RSTDOUT)]
    /\ rw_cells psegs mm 0xd1a38 [C8 (wz RSTDERR)]
    /\ rw_cells psegs mm RGOT_LLVMINIT [C8 (wz 0)]
    /\ rw_cells psegs mm 0xd1878 [C8 (wz 0xd1878)]
    /\ aex_inv mm.

  Definition estat_addr (a : Z) : Prop :=
    (0xe35c0 <= a < 0xe35e4) \/ (0x1038f0 <= a < 0x1038f8) \/ (0xd0850 <= a < 0xd0850 + 16) \/ (0xcac18 <= a < 0xcac20)
    \/ (0xd1b98 <= a < 0xd1b99) \/ (0xd06d8 <= a < 0xd06f0) \/ (0x103e60 <= a < 0x103e68) \/ (0x103e50 <= a < 0x103e58)
    \/ (0xd1b28 <= a < 0xd1b30) \/ (0xd1a38 <= a < 0xd1a40) \/ (0xd06f8 <= a < 0xd0730)
    \/ (0xd1878 <= a < 0xd1880) \/ aex_addr a.

  Definition BASE (mm : mem) : Prop :=
    stk psegs mm LO (usp0 + -128) /\ mem_inv psegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    /\ bytes_at psegs mm usp0 (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

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
      /\ (exists fl, sj_statics mm fl)
      /\ rw_cells psegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)]
      /\ stk psegs mm RSTAGE (RSTAGE + 65536).
End CTX.

Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt psegs (P1 sp0 argv envp uid TID) ms.

Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM psegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ psegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
