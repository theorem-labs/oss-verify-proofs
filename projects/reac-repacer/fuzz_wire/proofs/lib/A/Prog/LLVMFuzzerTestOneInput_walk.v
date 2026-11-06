(* wire_llvmf_holds: the image-A walk of fuzz_wire.asan's LLVMFuzzerTestOneInput meets its slot contract
   (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v wire_llvmf_holds_stmt). It is the composition wire_llvmf_holds_of_segs
   (LLVMFuzzerTestOneInput_segs.v) applied to the four segment theorems:
     entry    +0x000 .. +0x0a4, or +0x154 (the size refusal)   LLVMFuzzerTestOneInput_seg_entry.v  u_entry_ok
     turn_a   +0x0a4 .. +0x0fc (the seven checks)               LLVMFuzzerTestOneInput_seg_turna.v  u_turn_a_ok
     turn_b   +0x0fc .. +0x144 (malloc, memcpy, check_copy, check_read)
                                                                LLVMFuzzerTestOneInput_seg_turnb.v  u_turn_b_ok
     exit     +0x144 / +0x154 .. ret (the two frees, return 0)  LLVMFuzzerTestOneInput_seg_exit.v   u_exit_ok
   Every callee is a premise of wire_llvmf_holds_stmt; nothing else is assumed. wire_llvmf_holds_any holds at every
   record and value; wire_llvmf_holds is its instance at image A's record AD2l.WireB, the trivial meter, the zero cost
   bound and the read-only window [0x98288, 0x994e0). *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YM05 YG0d YG0f YG0n YCbq YC5d YO09 YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD2l.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require
  LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_turna LLVMFuzzerTestOneInput_seg_turnb
  LLVMFuzzerTestOneInput_seg_exit.
Open Scope Z_scope.

Theorem wire_llvmf_holds_any : forall (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops) (XL : Z -> Z) (RLO RHI : Z),
  @wire_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
  intros rc B MT XL RLO RHI.
  apply wire_llvmf_holds_of_segs.
  - apply LLVMFuzzerTestOneInput_seg_entry.u_entry_ok.
  - apply LLVMFuzzerTestOneInput_seg_turna.u_turn_a_ok.
  - apply LLVMFuzzerTestOneInput_seg_turnb.u_turn_b_ok.
  - apply LLVMFuzzerTestOneInput_seg_exit.u_exit_ok.
Qed.

Theorem wire_llvmf_holds : forall rc,
  @wire_llvmf_holds_stmt rc AD2l.WireB ameter_triv (fun _ => 0) 0x98288 0x994e0.
Proof. intros rc. apply wire_llvmf_holds_any. Qed.
