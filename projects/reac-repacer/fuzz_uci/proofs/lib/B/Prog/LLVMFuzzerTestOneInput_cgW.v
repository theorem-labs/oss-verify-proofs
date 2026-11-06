(* LLVMFuzzerTestOneInput_cgW: the image-B walk of fuzz_uci.asan-ubsan's LLVMFuzzerTestOneInput (0x7f2e8), the theorem
   uci_llvmf_holds : uci_llvmf_holds_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v, which discharges lib/B/UciBClose.v's
   H_PROG_LLVMF at UciB. It is the composition uci_llvmf_holds_of_segs (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v: the
   entry, then five turns by induction on the turn, then the exit) applied to the four segment theorems:
   u_entry_ok (+0x000 .. +0xbc, lib/B/Prog/LLVMFuzzerTestOneInput_seg_entry.v), u_turn_a_ok (+0xbc .. +0x180,
   _seg_turna.v), u_turn_b_ok (+0x180 .. the next head or +0x1c8, the calls of check_no_overread and check_value,
   _seg_turnb.v) and u_exit_ok (+0x1c8 .. ret, the call of check_clamp, _seg_exit.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YG0f.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_turna
  LLVMFuzzerTestOneInput_seg_turnb LLVMFuzzerTestOneInput_seg_exit.

Section walk. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem uci_llvmf_holds : @uci_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
  apply uci_llvmf_holds_of_segs.
  - apply u_entry_ok.
  - apply u_turn_a_ok.
  - apply u_turn_b_ok.
  - apply u_exit_ok.
Qed.
End walk.
