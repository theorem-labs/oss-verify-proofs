(* reac-pw/fuzz_link, image A (pin 059dae63e07c): the last flush of link's memory FILE at process exit, closed at
   link's instance.

   lib/A/Rt/LinkRwExitMw.v proves `amwrite_mf_flush_noar_realizes` for every B with PcapSyms B, under the
   memory-checking runtime's memcpy interceptor in its no-AR form. Here B = PcapB (lib/A/AD2l.v, PcapB_syms) and
   the interceptor is the frame's lib/A/AE31.v memcpy_icpt_noar_realizes at window ESTACK, whose entry MC_ENTRY
   0x52d74 is pc_wrap_memcpy Tfib_code (ts_code). No hypothesis is left. This is the theorem the exit lane cites for
   close_file's flush after the module destructor X2. Proves no function itself (kind: assembly). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AF0m AD2l AE2y AsanNoAR AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE31.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs LinkRwExitDefs LinkRwExitMw.
Local Open Scope Z_scope.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the memcpy interceptor mwrite calls at +0xc0, without AR *)
Lemma link_amemcpy_icpt_noar :
  aintrin_noar_realizes tfibsegs PcapB OCpy icpt_rodata ESTACK (pc_wrap_memcpy (as_code PcapB)).
Proof. rewrite (ts_code PcapB PcapB_syms). exact (AE31.memcpy_icpt_noar_realizes PcapB ESTACK (Z.le_refl _)). Qed.

Theorem amwrite_mf_flush_noar_ok : amwrite_mf_flush_noar_realizes tfibsegs PcapB link_amf icpt_rodata LA_MWRITE.
Proof.
  pose proof link_amemcpy_icpt_noar.
  apply link_amwrite_flush_noar; first [exact PcapB_syms | assumption].
Qed.

End I.

About amwrite_mf_flush_noar_ok.
Print Assumptions amwrite_mf_flush_noar_ok.
