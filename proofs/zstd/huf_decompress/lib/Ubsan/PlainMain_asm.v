(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_fprintf F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf F_vfprintf_stdout F_fwritex_stdout F_stdio_exit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import Harness_iface RDriver_iface RF_target_run RF_main PlainImpl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_PlainMain_asm () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission5UbsanAF_vfprintf_stdoutAemit_printf_proofC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=fuzz_one_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_malloc_spec<rmalloc_specC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_free_spec@rfree_spec_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_target_runAptarget_run_proofI5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00C5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_soC5ARocqVerifyHarness?AgentSubmission4Spec6PState9set_so_psC5ARocqVerifyHarness?AgentSubmission5Ubsan@F_fwritex_stdoutDfwritex_stdout_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan8F_fwriteAfwrite_diag_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan9F_fprintfBfprintf_diag_proofc5ARocqVerifyHarness?AgentSubmission5Ubsan=PlainMain_asmGplain_target_run_closedC5ARocqVerifyHarness?AgentSubmission5Ubsan7RF_main@plain_main_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan@F_fwritex_stderrDfwritex_stderr_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan=F_stdio_flushGstdio_write_flush_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan:F_vfprintf=towrite_proofc5ARocqVerifyHarness?AgentSubmission5Ubsan=PlainMain_asmAplain_main_closedC5ARocqVerifyHarness?AgentSubmission5Ubsan9PlainImplDplain_impl_from_mainI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00C5ARocqVerifyHarness?AgentSubmission5Ubsan<F_stdio_exitCstdio_exit_proof_ps".

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma plain_target_run_closed : fuzz_one_stmt -> ptarget_run_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_PlainMain_asm ()) ["CANSEC1"] "h04FUZZp;1p;3p;6p10000p4p70g000eR0p4p710R1p8p10023p4p70P1p8g002hj14Tg003nj13Tg0054j10TP0j31Tg006<j62Tp,2rcR0#4P0%30%00f0g007Fg008?g009531g009oE2W0o"). Qed.

(* [comment removed for export] *)
Lemma plain_main_closed : fuzz_one_stmt -> pmain_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_PlainMain_asm ()) ["CANSEC1"] "h04FUZZp;1p;9p10000p4p70R0g00;?R1p4p710R2p8P0g00<DR0p4p710R3p8p10023p4p70R4P2p8P4P3p8g002hj16Tg003nj15Tg0054j10TP0j11TP1j14Tg00=Kj12Tg00>[l93Tp,2rcR1#6P1%51%01g007FR1#1g00?^g00@n%41g00B>f0#2M93W0o"). Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem plain_impl : (forall rc : runConstT, @fuzz_one_stmt rc) ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_PlainMain_asm ()) [] "h02rch14FUZZp;1p;2g002hj12Tg00CAj21Tg00DKj20Tg00ETR0f0R1#2]0g00FQf1P1O1,11X00'0W1o"). Qed.
