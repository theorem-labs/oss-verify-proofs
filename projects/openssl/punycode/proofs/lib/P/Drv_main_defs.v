(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Layout Exit InitMem Startup Printf_stdio_iface Fz_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Exit_walk.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Exit_ax.     (* [comment removed for export] *)
From OSSVerify.openssl.punycode.images Require Import Plain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Plain.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.openssl.punycode.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.openssl.punycode.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.openssl.punycode.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.openssl.punycode.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x26b578.      (* [comment removed for export] *)
Definition RP1 : Z := 0xdccf4.            (* [comment removed for export] *)
Definition RUSAGE : Z := 0xdce7c.         (* [comment removed for export] *)
Definition RSTDERR_GOT : Z := 0x2d7590.    (* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeiling0.
Notation RSTAGE := 0x2d9309%Z (only parsing).
(* [comment removed for export] *)


Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  (* [comment removed for export] *)
  Definition ESTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0x2ebdc0 [C8 (wz 0x2ebdc0); C8 (wz 0x2ebdc0); C8 (wz 0x2ebdc0); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells psegs mm 0x30c0f8 [C4 (wz 0)]
    /\ rw_cells psegs mm 0x2d7b68 [C8 (wz 0x27bb60); C8 (wz 0x27bb50)]
    /\ rw_cells psegs mm 0x27bb50 [C8 (wz 0xdcc30); C8 (wz 0xe9a54)]
    /\ rw_cells psegs mm 0x2d9308 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x2d7580 [C8 (wz RCXA_FINALIZE); C8 (wz 0)]   (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x30c550 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x2d91b0 [C8 (wz RSTDIN)]
    /\ rw_cells psegs mm 0x2d92a0 [C8 (wz RSTDOUT)]
    /\ rw_cells psegs mm 0x2d90c0 [C8 (wz RSTDERR)]
    /\ rw_cells psegs mm RGOT_LLVMINIT [C8 (wz 0xdd1b8)]
    /\ rw_cells psegs mm 0x2e9548 [C1 (Z_to_bv 8 0)]          (* [comment removed for export] *)
    /\ stdin_file mm                                           (* [comment removed for export] *)
    /\ rw_cells psegs mm RDSO [C8 (wz RDSO)].                    (* [comment removed for export] *)

  Definition estat_addr (a : Z) : Prop :=
    (0x2ebdc0 <= a < 0x2ebde4) \/ (0x30c0f8 <= a < 0x30c100) \/ (0x2d7b68 <= a < 0x2d7b68 + 16) \/ (0x27bb50 <= a < 0x27bb60)
    \/ (0x2d9308 <= a < 0x2d9309) \/ (0x2d7580 <= a < 0x2d7590) \/ (0x30c550 <= a < 0x30c558) \/ (0x2d91b0 <= a < 0x2d91b8)
    \/ (0x2d92a0 <= a < 0x2d92a8) \/ (0x2d90c0 <= a < 0x2d90c8) \/ (0x2d7598 <= a < 0x2d75a8)
    \/ (0x2e9548 <= a < 0x2e9549) \/ (0x2d90c8 <= a < 0x2d91b0) \/ (0x2d8b78 <= a < 0x2d8b80).

  (* [comment removed for export] *)
  Definition BASE (mm : mem) : Prop :=
    stk psegs mm LO (usp0 + -128) /\ mem_inv psegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    /\ bytes_at psegs mm usp0 (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

  (* [comment removed for export] *)
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
      /\ (exists fl, lx_flags mm fl)
      /\ rw_cells psegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)]
      /\ stk psegs mm RSTAGE (RSTAGE + 65536)
      /\ AXSTAT false mm.                                      (* [comment removed for export] *)
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt psegs (P1 sp0 argv envp uid TID) ms.

(* [comment removed for export] *)
Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM psegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ psegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
