(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg Harness_iface RF_huf_h_final PlainMain_asm.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_PlainClosed () := "C59OSSVerify5KrLib5Ubsan>RF_huf_h_final>fuzz_one_finalC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan;PlainClosedAplain_fuzz_closedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=PlainMain_asm:plain_implC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma plain_fuzz_closed : fuzz_one_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_PlainClosed ()) ["CANSEC1"] "p;1g0000j10Tp,2rc#0o"). Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem plain_impl_closed : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_PlainClosed ()) [] "h02rcp;1g0018j11Tg002@j10Tg003Cf0#1W0#0o"). Qed.
