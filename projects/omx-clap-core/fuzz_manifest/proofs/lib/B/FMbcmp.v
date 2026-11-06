(* B twin (fm.asan-ubsan) of lib/A/FMbcmp.v at a working branch 9261fc100fc.
   The bcmp wrapper's contract at fuzz_manifest's symbol on image B: abcmp_realizes at PC_bcmp (lib/B/FMH_Base.v,
   0x41348 = __interceptor_trampoline_bcmp in fuzz_manifest.asan-ubsan). It is ReusableB/YE2s.v bcmp_icpt_contract,
   a Theorem Labs lane's relocation of the donor proof (cgif_file_fuzzer lib/A/AE2s.v:710) onto image B (core2 e70bcdbfb7d).
   fm_bcmp_TfibB is the form that G4's expected_spec_holds instance takes (its BCMP premise). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YG0d YG0q YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YD2l YE2s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem fm_bcmp_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> abcmp_realizes tfibsegs B PC_bcmp.
Proof. intros B LAWS TB. exact (bcmp_icpt_contract B LAWS TB). Qed.

Theorem fm_bcmp_TfibB : abcmp_realizes tfibsegs TfibB PC_bcmp.
Proof. exact (fm_bcmp_contract TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.

End a.
