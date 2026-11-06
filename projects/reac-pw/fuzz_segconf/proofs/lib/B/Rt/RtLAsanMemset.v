(* __asan_memset of fuzz_command.asan (0x57acc; A/AF0l.v:14 pc_asan_memset): the model's contract aintrin_realizes
   OSet at pc_asan_memset (YG0d.v:326-344, the record field aa_asan_memset, YG0d.v:547), with no premise beyond AR_laws
   and SegBSyms. Ported from cgif AE2r.v:566 (released): relocated by the core relocator into A/AE2r.v and its closure
   A/AE6t.v .. A/AE6v.v (code equal modulo pc-relative fields); instanced as cgif
   instances it (cgif lib/A/ACed.v:145 tfibX_AMEMSET: the walk states amem_range last, the contract before the
   OSet arm). *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLAsanMemset.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0l YF0m YE2r.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem cmd_asan_memset : forall B, AR_laws tfibsegs B -> SegBSyms B ->
  aintrin_realizes tfibsegs B OSet (pc_asan_memset (as_code B)).
Proof.
  intros B LAWS TB. rewrite (ts_code B TB).
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (asan_memset_realizes B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
End b.
