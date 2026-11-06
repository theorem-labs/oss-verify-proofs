(* LLVMFuzzerTestOneInput_walk: the image-B walk of fuzz_wire.asan-ubsan's LLVMFuzzerTestOneInput (0x7fbf8), the theorem
   wire_llvmf_holds : wire_llvmf_holds_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v. It is the composition
   wire_llvmf_holds_of_segs (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v: the entry, then turn_a, turn_b and the exit, or
   the exit at once after the size refusal) applied to the four segment theorems: u_entry_ok (+0x000 .. +0xb0, or
   +0x160 on the refusal, lib/B/Prog/LLVMFuzzerTestOneInput_seg_entry.v), u_turn_a_ok (+0xb0 .. +0x108, the seven checks
   on f, _seg_turna.v), u_turn_b_ok (+0x108 .. +0x150: the malloc of c, its copy, check_copy and check_read,
   _seg_turnb.v) and u_exit_ok (+0x150 or +0x160 .. ret: the two frees and the return, _seg_exit.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YG0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_turna
  LLVMFuzzerTestOneInput_seg_turnb LLVMFuzzerTestOneInput_seg_exit.

Section walk. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem wire_llvmf_holds : @wire_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
  apply wire_llvmf_holds_of_segs.
  - apply u_entry_ok.
  - apply u_turn_a_ok.
  - apply u_turn_b_ok.
  - apply u_exit_ok.
Qed.
End walk.
