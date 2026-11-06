(* uci_llvmf_holds: the image-A walk of fuzz_uci.asan's LLVMFuzzerTestOneInput meets its slot contract
   (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v uci_llvmf_holds_stmt). It is the composition uci_llvmf_holds_of_segs
   (LLVMFuzzerTestOneInput_segs.v, which also runs the five turns of the loop) applied to the four segment theorems:
     entry    +0x000 .. +0x0a8   LLVMFuzzerTestOneInput_seg_entry.v  u_entry_ok
     turn_a   +0x0a8 .. +0x130   LLVMFuzzerTestOneInput_seg_turna.v  u_turn_a_ok
     turn_b   +0x130 .. +0x0a8 / +0x180   LLVMFuzzerTestOneInput_seg_turnb.v  u_turn_b_ok
     exit     +0x180 .. ret      LLVMFuzzerTestOneInput_seg_exit.v   u_exit_ok
   Every callee is a premise of uci_llvmf_holds_stmt; nothing else is assumed. uci_llvmf_holds_any holds at every
   record and value; uci_llvmf_holds is its instance at image A's record AD2l.UciB, the trivial meter, the zero cost
   bound and the read-only window [0x96ac0, 0x97d18). *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YM05 YG0d YG0f YG0n YCbq YC5d YO09 YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AD2l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require
  LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_turna LLVMFuzzerTestOneInput_seg_turnb
  LLVMFuzzerTestOneInput_seg_exit.
Open Scope Z_scope.

Theorem uci_llvmf_holds_any : forall (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops) (XL : Z -> Z) (RLO RHI : Z),
  @uci_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
  intros rc B MT XL RLO RHI.
  apply uci_llvmf_holds_of_segs.
  - apply LLVMFuzzerTestOneInput_seg_entry.u_entry_ok.
  - apply LLVMFuzzerTestOneInput_seg_turna.u_turn_a_ok.
  - apply LLVMFuzzerTestOneInput_seg_turnb.u_turn_b_ok.
  - apply LLVMFuzzerTestOneInput_seg_exit.u_exit_ok.
Qed.

Theorem uci_llvmf_holds : forall rc,
  @uci_llvmf_holds_stmt rc AD2l.UciB ameter_triv (fun _ => 0) 0x96ac0 0x97d18.
Proof. intros rc. apply uci_llvmf_holds_any. Qed.
