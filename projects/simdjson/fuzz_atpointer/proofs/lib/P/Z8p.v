(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio Zpb Target Driver Prog StrFun.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zcp Startup Zfq Zq5 Z8e Z8h Z8f.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := Zf2.wz.
Notation pph := Plain.M.phdrs.

From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Z7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x642b4.
Definition RP1 : Z := 0x26cf4.
Definition RUSAGE : Z := 0x26e5c.
Definition RSTDERR_GOT : Z := 0x77858.

End WithCeiling0.
Notation RSTAGE := 0x78c19%Z (only parsing).

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
    rw_cells psegs mm 0x89788 [C8 (wz 0x89788); C8 (wz 0x89788); C8 (wz 0x89788); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells psegs mm 0xa9ab8 [C4 (wz 0)]
    /\ rw_cells psegs mm 0x77968 [C8 (wz 0x74530); C8 (wz 0x74528)]
    /\ rw_cells psegs mm 0x74528 [C8 (wz 0x26c34)]
    /\ rw_cells psegs mm 0x78c18 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x77848 [C8 (wz 0x6471c); C8 (wz 0)]
    /\ rw_cells psegs mm 0xa9f10 [C8 (wz 0)]
    /\ rw_cells psegs mm 0xa9f00 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x78bb8 [C8 (wz RSTDOUT)]
    /\ rw_cells psegs mm 0x78ac8 [C8 (wz RSTDERR)]
    /\ rw_cells psegs mm RGOT_LLVMINIT [C8 (wz 0)]
    /\ rw_cells psegs mm 0x78978 [C8 (wz 0x78978)]
    /\ aex_inv mm.

  Definition estat_addr (a : Z) : Prop :=
    (0x89788 <= a < 0x897ac) \/ (0xa9ab8 <= a < 0xa9ac0) \/ (0x77968 <= a < 0x77968 + 16) \/ (0x74528 <= a < 0x74530)
    \/ (0x78c18 <= a < 0x78c19) \/ (0x77848 <= a < 0x77858) \/ (0xa9f10 <= a < 0xa9f18) \/ (0xa9f00 <= a < 0xa9f08)
    \/ (0x78bb8 <= a < 0x78bc0) \/ (0x78ac8 <= a < 0x78ad0) \/ (0x77860 <= a < 0x77878)
    \/ (0x78978 <= a < 0x78980) \/ aex_addr a.

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
