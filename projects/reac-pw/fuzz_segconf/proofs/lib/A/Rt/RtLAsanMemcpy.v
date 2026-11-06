(* __asan_memcpy of fuzz_command.asan (0x57630, its own body; A/AF0l.v:14 pc_asan_memcpy): the model's contract
   aintrin_realizes OCpy at pc_asan_memcpy (YG0d.v:326-344, the record field aa_asan_memcpy, YG0d.v:546), with no
   premise beyond AR_laws and SegBSyms. Ported from cgif AE2q.v:143 (released): relocated by the core relocator into
   A/AE2q.v and its closure A/AE6k.v .. A/AE6s.v (code equal modulo pc-relative fields);
   instanced as cgif instances it (cgif lib/A/ACed.v:150 tfibX_AMEMCPY) and as A/AD1o.v:72 instances the interceptor. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0l AF0m AE2q.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem cmd_asan_memcpy : forall B, AR_laws tfibsegs B -> SegBSyms B ->
  aintrin_realizes tfibsegs B OCpy (pc_asan_memcpy (as_code B)).
Proof. intros B LAWS TB. rewrite (ts_code B TB). exact (asan_memcpy_realizes B LAWS TB). Qed.
End b.
