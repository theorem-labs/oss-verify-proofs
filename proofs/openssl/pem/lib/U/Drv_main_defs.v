(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Startup Printf_stdio_iface Fz_iface Driver_iface Drv_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_ax.     (* [comment removed for export] *)
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x2b0064.      (* [comment removed for export] *)
Definition RP1 : Z := 0xe15ec.            (* [comment removed for export] *)
Definition RUSAGE : Z := 0xe1774.         (* [comment removed for export] *)
Definition RSTDERR_GOT : Z := 0x31bed0.    (* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeiling0.
Notation RSTAGE := 0x31dde9%Z (only parsing).
(* [comment removed for export] *)


Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variable C : cli_sig.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells usegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  (* [comment removed for export] *)
  Definition ESTAT (mm : mem) : Prop :=
    rw_cells usegs mm 0x3308a0 [C8 (wz 0x3308a0); C8 (wz 0x3308a0); C8 (wz 0x3308a0); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells usegs mm 0x350bd8 [C4 (wz 0)]
    /\ rw_cells usegs mm 0x31c498 [C8 (wz 0x2c0650); C8 (wz 0x2c0640)]
    /\ rw_cells usegs mm 0x2c0640 [C8 (wz 0xe1528); C8 (wz 0xe1c74)]
    /\ rw_cells usegs mm 0x31dde8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0x31bec0 [C8 (wz RCXA_FINALIZE); C8 (wz 0)]   (* [comment removed for export] *)
    /\ rw_cells usegs mm 0x351030 [C8 (wz 0)]
    /\ rw_cells usegs mm 0x31dc88 [C8 (wz RSTDIN)]
    /\ rw_cells usegs mm 0x31dd78 [C8 (wz RSTDOUT)]
    /\ rw_cells usegs mm 0x31db98 [C8 (wz RSTDERR)]
    /\ rw_cells usegs mm RGOT_LLVMINIT [C8 (wz 0xe1ab0)]
    /\ rw_cells usegs mm 0x32de24 [C1 (Z_to_bv 8 0)]          (* [comment removed for export] *)
    /\ stdin_file mm                                           (* [comment removed for export] *)
    /\ rw_cells usegs mm RDSO [C8 (wz RDSO)].                    (* [comment removed for export] *)

  Definition estat_addr (a : Z) : Prop :=
    (0x3308a0 <= a < 0x3308c4) \/ (0x350bd8 <= a < 0x350be0) \/ (0x31c498 <= a < 0x31c498 + 16) \/ (0x2c0640 <= a < 0x2c0650)
    \/ (0x31dde8 <= a < 0x31dde9) \/ (0x31bec0 <= a < 0x31bed0) \/ (0x351030 <= a < 0x351038) \/ (0x31dc88 <= a < 0x31dc90)
    \/ (0x31dd78 <= a < 0x31dd80) \/ (0x31db98 <= a < 0x31dba0) \/ (0x31bed8 <= a < 0x31bee8)
    \/ (0x32de24 <= a < 0x32de25) \/ (0x31dba0 <= a < 0x31dc88) \/ (0x31d4a8 <= a < 0x31d4b0).

  (* [comment removed for export] *)
  Definition BASE (mm : mem) : Prop :=
    stk usegs mm LO (usp0 + -128) /\ mem_inv usegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    /\ bytes_at usegs mm usp0 (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

  (* [comment removed for export] *)
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
      /\ (exists fl, lx_flags mm fl)
      /\ rw_cells usegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)]
      /\ stk usegs mm RSTAGE (RSTAGE + 65536)
      /\ CLI0 C mm                                            (* [comment removed for export] *)
      /\ AXSTAT false mm.                                      (* [comment removed for export] *)
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition main_to_P1_stmt (C : cli_sig) : Prop :=
  cli0_at_main C ->
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt usegs (P1 C sp0 argv envp uid TID) ms.

(* [comment removed for export] *)
Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM usegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ usegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
