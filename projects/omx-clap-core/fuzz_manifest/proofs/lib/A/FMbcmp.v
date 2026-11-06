(* The bcmp wrapper's contract at fuzz_manifest's symbol: abcmp_realizes at PC_bcmp (FMH_Base.v), the address of
   __interceptor_trampoline_bcmp (the 4-byte jump to ___interceptor_bcmp) in fuzz_manifest.asan. It is the relocated
   donor proof A/AE2s.v bcmp_icpt_contract (cgif_file_fuzzer lib/A/AE2s.v:710). fm_bcmp_TfibB is the form that
   FMAsm.v's expected_spec_holds instance takes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YG0d YG0q YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AD2l FMH_Base AE2s.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem fm_bcmp_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> abcmp_realizes tfibsegs B PC_bcmp.
Proof. intros B LAWS TB. exact (bcmp_icpt_contract B LAWS TB). Qed.

Theorem fm_bcmp_TfibB : abcmp_realizes tfibsegs TfibB PC_bcmp.
Proof. exact (fm_bcmp_contract TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.

End a.
