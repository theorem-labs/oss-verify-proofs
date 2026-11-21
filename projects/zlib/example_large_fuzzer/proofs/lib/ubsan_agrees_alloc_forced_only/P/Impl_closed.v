(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite F_fprintf F_vfprintf_stdout
  Zlib_iface Zl_iface Driver_iface Drv_kit Drv_target Drv_main Impl Zh_closed F_calloc.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RCalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_example_large_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rtarget_run_closed : rfuzz_oneL_stmt -> rtarget_run_stmt.
Proof.
  intros FUZZ.
  exact (rtarget_run_proof rmalloc_spec rfree_spec_proof rfree_null_spec FUZZ
           (emit_printf_proof PState ps_so set_so_ps) fwritex_stdout_ok
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.

(* [comment removed for export] *)
Lemma rmain_closed : rfuzz_oneL_stmt -> rmain_stmt.
Proof.
  intros FUZZ.
  exact (main_proof rmalloc_spec rfree_spec_proof (fprintf_diag_proof PState) fwritex_stderr_ok stdio_write_flush_ok
           (fwrite_diag_proof towrite_proof) (rtarget_run_closed FUZZ)).
Qed.
End WithCeiling0.

(* [comment removed for export] *)
Theorem impl_P_closed : (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_oneL_stmt CE__ RN__) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Src_zlib_example_large_fuzzer_repro.M.init_pc Src_zlib_example_large_fuzzer_repro.M.phdrs) en inp ->
    valid_input inp ->
    impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs Src_zlib_example_large_fuzzer_repro.M.init_pc Src_zlib_example_large_fuzzer_repro.M.phdrs en inp).
Proof. intros FUZZ. exact (impl_P_from_main (fun CE__ RN__ => @rmain_closed CE__ RN__ (FUZZ CE__ RN__))). Qed.

(* [comment removed for export] *)
Theorem impl_P_of_zlib : forall R : Ceiling -> zrepsL,
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_okL CE__ RN__ (R CE__)) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs Src_zlib_example_large_fuzzer_repro.M.init_pc Src_zlib_example_large_fuzzer_repro.M.phdrs) en inp ->
    valid_input inp ->
    impl psegs (at_node psegs) (@prog (ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs Src_zlib_example_large_fuzzer_repro.M.init_pc Src_zlib_example_large_fuzzer_repro.M.phdrs en inp).
Proof.
  intros R ZOK. exact (impl_P_closed (fun CE__ RN__ => @rfuzz_one_of_zlib CE__ RN__ (R CE__) (ZOK CE__ RN__) (@rcalloc_proof CE__ RN__))).
Qed.
