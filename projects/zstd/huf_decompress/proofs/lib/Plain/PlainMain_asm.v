(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_fprintf F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf F_vfprintf_stdout F_fwritex_stdout F_stdio_exit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Harness_iface RDriver_iface RF_target_run RF_main PlainImpl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_PlainMain_asm () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_vfprintf_stdoutAemit_printf_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_iface=fuzz_one_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_malloc_spec<rmalloc_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RF_free_spec@rfree_spec_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_target_runAptarget_run_proofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_fwritex_stdoutDfwritex_stdout_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_fwriteAfwrite_diag_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_fprintfBfprintf_diag_proofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=PlainMain_asmGplain_target_run_closedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain7RF_main@plain_main_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_fwritex_stderrDfwritex_stderr_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=F_stdio_flushGstdio_write_flush_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_vfprintf=towrite_proofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=PlainMain_asmAplain_main_closedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9PlainImplDplain_impl_from_mainC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<F_stdio_exitCstdio_exit_proof_psC1?~~~~~~~~~~~~~~~".

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
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
    valid_input_either inp ->
    impl psegs (at_node psegs) (Prog.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs p_init_pc p_phdrs en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_PlainMain_asm ()) [] "h02rch14FUZZp;1p;2g002hj12Tg00CAj21Tg00DKj20Tg00ETR0f0R1#2]0g00FQf1P1O1,11X00'0W1o"). Qed.
