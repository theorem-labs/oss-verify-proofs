(* __asan_memcpy of fuzz_command.asan-ubsan (image B: 0x5767c, its own body; B/YF0l.v:15 pc_asan_memcpy): the
   model's contract aintrin_realizes OCpy at pc_asan_memcpy (YG0d.v:326-344, the record field aa_asan_memcpy,
   YG0d.v:546), with no premise beyond AR_laws and CmdBSyms. The image-A text lib/A/Rt/RtLAsanMemcpy.v (cgif AE2q.v:143,
   released, relocated by the core relocator) moved to image B: B/YE2q.v and its closure B/YE6k.v .. B/YE6s.v,
   B/YE3c.v are the A-to-B address mapper's twins of the A files (B's __asan_memcpy, __asan_region_is_poisoned and
   musl memcpy are A's code modulo pc-relative fields, no UBSan call). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0l YF0m YE2q.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem cmd_asan_memcpy : forall B, AR_laws tfibsegs B -> CmdBSyms B ->
  aintrin_realizes tfibsegs B OCpy (pc_asan_memcpy (as_code B)).
Proof. intros B LAWS TB. rewrite (ts_code B TB). exact (asan_memcpy_realizes B LAWS TB). Qed.
End b.
