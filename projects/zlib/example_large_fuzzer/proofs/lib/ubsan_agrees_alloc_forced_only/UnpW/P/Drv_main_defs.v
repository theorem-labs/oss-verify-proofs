(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Driver. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Exit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Startup Printf_stdio_iface Zlib_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_example_large_fuzzer_repro.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := SrcO_zlib_example_large_fuzzer_repro.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x201fc.      (* [comment removed for export] *)
Definition RP1 : Z := 0x159fc.            (* [comment removed for export] *)
Definition RUSAGE : Z := 0x15b64.         (* [comment removed for export] *)
Definition RSTDERR_GOT : Z := 0x29420.    (* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeiling0.
Notation RSTAGE := 0x2a6d9%Z (only parsing).
(* [comment removed for export] *)


Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition LO : Z := usp0 - 6144513.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  (* [comment removed for export] *)
  Definition ESTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0x3a728 [C8 (wz 0x3a728); C8 (wz 0x3a728); C8 (wz 0x3a728); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells psegs mm 0x5aa50 [C4 (wz 0)]
    /\ rw_cells psegs mm 0x29470 [C8 (wz 0x29280); C8 (wz 0x29278)]
    /\ rw_cells psegs mm 0x29278 [C8 (wz 0x1593c)]
    /\ rw_cells psegs mm 0x2a6d8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x29410 [C8 (wz 0x20578); C8 (wz 0)]         (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x2a480 [C8 (wz 0x2a480)]                   (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x5aea8 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x5ae98 [C8 (wz 0)]
    /\ rw_cells psegs mm 0x2a680 [C8 (wz RSTDOUT)]
    /\ rw_cells psegs mm 0x2a590 [C8 (wz RSTDERR)]
    /\ rw_cells psegs mm RGOT_LLVMINIT [C8 (wz 0)].

  Definition estat_addr (a : Z) : Prop :=
    (0x3a728 <= a < 0x3a74c) \/ (0x5aa50 <= a < 0x5aa50 + 4) \/ (0x29470 <= a < 0x29470 + 16) \/ (0x29278 <= a < 0x29280)
    \/ (0x2a6d8 <= a < 0x2a6d9) \/ (0x29410 <= a < 0x29420) \/ (0x5aea8 <= a < 0x5aeb0) \/ (0x5ae98 <= a < 0x5aea0)
    \/ (0x2a680 <= a < 0x2a688) \/ (0x2a590 <= a < 0x2a598) \/ (0x29428 <= a < 0x29428 + 8) \/ (0x2a480 <= a < 0x2a480 + 8).

  (* [comment removed for export] *)
  Definition BASE (mm : mem) : Prop :=
    stk psegs mm LO (usp0 + -128) /\ mem_inv psegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    (* port727 (a worker): the entry block is the family's img_at ('s build_stack_bytes), the
       conjunct at_main states *)
    /\ bytes_at psegs mm usp0 (img_at sp0 argv envp uid).

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
      /\ zl_statics0 mm                                           (* [comment removed for export] *)
      /\ rdrv_statics mm                                           (* [comment removed for export] *)
      /\ stk psegs mm RSTAGE (RSTAGE + 65536).
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt psegs (P1 sp0 argv envp uid TID) ms.

(* [comment removed for export] *)
Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM psegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ psegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.
