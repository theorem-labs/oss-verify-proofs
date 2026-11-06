(* __asan_memset of fuzz_command.asan (0x57acc; A/AF0l.v:14 pc_asan_memset): the model's contract aintrin_realizes
   OSet at pc_asan_memset (YG0d.v:326-344, the record field aa_asan_memset, YG0d.v:547), with no premise beyond AR_laws
   and CmdBSyms. Ported from cgif AE2r.v:566 (released): relocated by the core relocator into A/AE2r.v and its closure
   A/AE6t.v .. A/AE6v.v (code equal modulo pc-relative fields); instanced as cgif
   instances it (cgif lib/A/ACed.v:145 tfibX_AMEMSET: the walk states amem_range last, the contract before the
   OSet arm). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0l AF0m AE2r.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem cmd_asan_memset : forall B, AR_laws tfibsegs B -> CmdBSyms B ->
  aintrin_realizes tfibsegs B OSet (pc_asan_memset (as_code B)).
Proof.
  intros B LAWS TB. rewrite (ts_code B TB).
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (asan_memset_realizes B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
End b.
