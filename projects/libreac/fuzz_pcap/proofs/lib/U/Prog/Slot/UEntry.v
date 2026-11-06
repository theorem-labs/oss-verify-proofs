From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import bcmp_c memcpy_c rd32f_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require bcmp memcpy rd32f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PLink UCut UCall
  UGlueT UGlueW UGlueR7 UGlueF UGlueA UGlueE.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.
From OSSVerify.libreac.fuzz_pcap Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* The run of the ubsan slot from its entry: the front (E, A, B, C), the walk and the tail, chained through the
   cuts of UCut.v. Its output is PWalk.OUT of the payload. *)

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Let HNEXT : forall fx0 : YK11.FPState, @pcap_source_next_c.pcap_source_next_contract fx0 := uc_next.
Let HCLOSE : forall fx0 : YK11.FPState, @pcap_source_close_c.pcap_source_close_contract fx0 rc B (APIf rc) :=
  fun fx0 => @uc_close fx0 rc B APIf SH SK ra empty FF.
Let HOPEN : forall fx0 : YK11.FPState, @pcap_source_open_c.pcap_source_open_contract fx0 rc B (APIf rc) :=
  fun fx0 => @uc_open fx0 rc B APIf SH SK ra empty FF.

(* From the cut after the first answer (0x12e04) to the end. *)
Lemma ue_K12e3c : Hcut_o B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24).
Proof.
  apply (ug_K12e3c B APIf ra empty FF HCLOSE bcmp.bcmp_holds HNEXT).
  apply (ug_tail B APIf ra empty FF HNEXT HCLOSE HOPEN).
  exact (ug_R7 B APIf ra empty FF).
Qed.

Lemma ue_K1310c : HCT B APIf ra (Inv_K1310c B APIf ra empty).
Proof. exact (ug_R7 B APIf ra empty FF). Qed.

(* From the cut after the open (0x12d38) to the end: segment B, the record buffer's malloc or the refused path's
   free, segment C and the first call of the walk. *)
Lemma ue_K12d70 : Hcut_o B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PWalk.OUT (g_in g)).
Proof.
  eapply ug_B.
  all: try first [exact FF | exact HOPEN | exact HNEXT | exact ue_K1310c].
  eapply ug_C.
  all: try first [exact FF | exact HOPEN | exact HNEXT | exact ue_K12e3c].
Qed.

(* The whole run from the entry. *)
Lemma ue_entry : Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PWalk.OUT (g_in g)).
Proof.
  apply (ug_E B APIf ra empty FF).
  apply (ug_A B APIf ra empty FF memcpy.memcpy_holds).
  exact ue_K12d70.
Qed.

End E.

(* The statement from the run of the slot cut at its entry. *)
Lemma ue_halts_of_entry :
  (forall (fx : YK11.FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
          (SH : sink_head) (SK : sink_syms) (ra empty : Z),
     frame_facts B APIf SH SK ra empty ->
     Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PWalk.OUT (g_in g))) ->
  OSSVerify.libreac.fuzz_pcap.Statements.ubsan_halts.
Proof.
  intros H. apply (ubsan_halts_of_entry_o PWalk.OUT).
  - intros fx rc B APIf SH SK ra empty FF _ _. exact (H fx rc B APIf SH SK ra empty FF).
  - exact PWalk.OUT_big.
Qed.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_pcap.Statements.ubsan_halts.
Proof.
  apply ue_halts_of_entry. intros fx rc B APIf SH SK ra empty FF. exact (@ue_entry fx rc B APIf SH SK ra empty FF).
Qed.
