From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import pcap_source_open_c pcap_source_close_c
  pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require libreac_fuzz_fopen_c pcap_source_open pcap_source_close pcap_source_next
  libreac_fuzz_fopen fclose fmemopen fflush mseek mclose __unlist_locked_file __ofl_lock __ofl_unlock __ofl_add
  __lock __unlock strchr strcmp memset memcpy fread_ro memmove_ro rd_u32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac.
Import ListNotations.
Open Scope Z_scope.

(* The reader contracts of the slot's calls, from their proofs and the frame's facts. *)
Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma uc_fclose : fclose_c.fclose_contract B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ALLOC rc fx) as (HMAL & HFREE & HFREE0 & _ & _ & _ & _ & _ & _ & HBW & _ & _ & _ & HAX & _).
  apply fclose.fclose_holds; try assumption.
  - apply fflush.fflush_holds. exact mseek.mseek_holds.
  - exact mclose.mclose_holds.
  - exact __unlist_locked_file.__unlist_locked_file_holds.
  - apply __ofl_lock.__ofl_lock_holds. exact __lock.__lock_holds.
  - apply __ofl_unlock.__ofl_unlock_holds. exact __unlock.__unlock_holds.
Qed.

Lemma uc_fmemopen : fmemopen_c.fmemopen_contract B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ALLOC rc fx) as (HMAL & HFREE & HFREE0 & _ & _ & _ & _ & _ & _ & HBW & _ & _ & HNL & HAX & _).
  apply fmemopen.fmemopen_holds; try assumption.
  - exact strchr.strchr_holds.
  - exact memset.memset_holds.
  - apply __ofl_add.__ofl_add_holds.
    + apply __ofl_lock.__ofl_lock_holds. exact __lock.__lock_holds.
    + apply __ofl_unlock.__ofl_unlock_holds. exact __unlock.__unlock_holds.
Qed.

Lemma uc_open : pcap_source_open_contract B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & _).
  destruct (ss_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAX & _).
  assert (HFO : libreac_fuzz_fopen_c.libreac_fuzz_fopen_contract B (APIf rc))
    by (apply libreac_fuzz_fopen.libreac_fuzz_fopen_holds;
        first [exact (ERRC rc) | exact strcmp.strcmp_holds | exact uc_fmemopen]).
  apply pcap_source_open.pcap_source_open_holds;
    first [exact (ERRC rc) | exact HAX | exact HFO | exact fread_ro.fread_ro_holds | exact uc_fclose].
Qed.

Lemma uc_close : pcap_source_close_contract B (APIf rc).
Proof.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & _).
  apply pcap_source_close.pcap_source_close_holds; first [exact (ERRC rc) | exact uc_fclose].
Qed.

End C.

Lemma uc_next : forall fx : YK11.FPState, @pcap_source_next_contract fx.
Proof.
  intros fx. apply pcap_source_next.pcap_source_next_holds.
  - exact fread_ro.fread_ro_holds.
  - exact (memmove_ro.memmove_ro_holds memcpy.memcpy_holds).
  - exact rd_u32.rd_u32_holds.
Qed.
