From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct_next
  pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PWalk PCut PGlueD PGlueE PGlueB
  PGlueR PGlueRN PGlueL PGlueAC PTop.
From OSSVerify.libreac.fuzz_pcap Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* The glue lemmas of every cut (PGlueE, PGlueAC, PGlueB, PGlueR, PGlueRN, PGlueL, PGlueD) for any frame instance;
   their callee contracts come from top_contracts. *)
Lemma pcap_glue : forall (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts B APIf SH SK ra empty -> top_contracts B APIf -> top_glue B APIf ra empty.
Proof.
  intros rc B APIf SH SK ra empty FF HT.
  pose proof HT as (HOPEN & HCLOSE & HNEXT & _ & _).
  split; [exact (seg_E B APIf ra empty FF)|].
  split; [intros H1 H2; eapply seg_A; eauto|].
  split; [exact (seg_B_good B APIf ra empty FF)|].
  split; [exact (seg_B_ref B APIf ra empty FF)|].
  split; [intros H; eapply seg_C; eauto|].
  split; [intros i p Hi H; eapply seg_L; eauto|].
  split; [intros H; eapply seg_W; eauto|].
  split; [intros H; eapply seg_R1; eauto|].
  split; [intros H; eapply seg_R2; eauto|].
  split; [intros H; eapply seg_R3; eauto|].
  split; [intros H; eapply seg_R4; eauto|].
  split; [exact (seg_R5 B APIf ra empty FF)|].
  split; [exact (seg_R6 B APIf ra empty FF)|].
  exact (seg_R7 B APIf ra empty FF).
Qed.

(* The slot's run from its entry for any frame instance. *)
Lemma pcap_entry : forall (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts B APIf SH SK ra empty -> Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Proof.
  intros rc B APIf SH SK ra empty FF.
  exact (entry_of_glue B APIf ra empty FF (pcap_glue rc B APIf SH SK ra empty FF (top_contracts_holds B APIf ra empty FF))).
Qed.

(* Statements.plain_halts of fuzz_pcap. *)
Theorem pcap_plain_halts_holds : OSSVerify.libreac.fuzz_pcap.Statements.plain_halts.
Proof. apply plain_halts_holds_of_glue. exact pcap_glue. Qed.
