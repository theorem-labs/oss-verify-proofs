(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit Exit_defs Startup Printf_stdio_iface Lib_iface Driver_iface Drv_kit.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Definition RMAIN_RET : Z := 0x2b0530.
Definition RP1 : Z := 0xe15ec.
Definition RUSAGE : Z := 0xe1774.
Definition RSTDERR_GOT : Z := 0x31c500.

End WithCeiling0.
Notation RSTAGE := 0x31e419%Z (only parsing).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 8388608.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells bgusegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  Definition ESTATr (reg : bool) (mm : mem) : Prop :=
    exit_statics TID mm /\ rw_cells bgusegs mm RGOT_LLVMINIT [C8 (wz LX_INIT)]
    /\ atexit_cells_st reg mm.
  Definition ESTAT (mm : mem) : Prop := ESTATr false mm.

  Definition estat0_addr (a : Z) : Prop := exit_statics_addr a \/ (0x31c508 <= a < 0x31c510).
  Definition estat_addr (a : Z) : Prop :=
    exit_statics_addr a \/ (0x31c508 <= a < 0x31c510)
    \/ (0x350fe8 <= a < 0x351010) \/ (0x351108 <= a < 0x351110) \/ (0x32e424 <= a < 0x32e425).

  Definition BASE (mm : mem) : Prop :=
    stk bgusegs mm LO (usp0 + -128) /\ mem_inv bgusegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    /\ bytes_at bgusegs mm usp0 (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
      ms = MS (mkR (wz RMAIN_RET) (wz (usp0 + -128)) (wz 0x10800) (wz RATP) t0 t1 t2
                   (wz 2) (wz 2) (wz 2) (wz (usp0 + 8)) (wz (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (wz RMAIN) (wz (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (wz RP1) (Z_to_bv 32 0) None mm (seg_rom bgusegs)
      /\ MFRAME mm pad s7 s6 s5 s4 /\ BASE mm
      /\ RHEAP (ps_init (reservedZ bgusegs)) [] mm
      /\ rw_cells bgusegs mm (errno_addr (wz RATP)) [C4 (wz 0)]
      /\ stdout_file mm stdout_init /\ stderr_wfile0 mm

      /\ rw_cells bgusegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)]
      /\ stk bgusegs mm RSTAGE (RSTAGE + 65536)

      /\ ossl_exit_cells mm /\ lib_pristine mm.
End CTX.

Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt bgusegs (P1 sp0 argv envp uid TID) ms.

Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM bgusegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ bgusegs))
          (fun code s' ms' => at_exit code s' ms') ms.
End WithCeiling1.
