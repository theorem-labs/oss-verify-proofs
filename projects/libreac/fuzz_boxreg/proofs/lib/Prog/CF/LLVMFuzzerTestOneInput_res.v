From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma llvm_name_room : forall stk empty L0 A0 regs0 mem0 md0 ra p n b nm,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b -> 0 <= nm <= LLVM_REQ ->
  room_ag (sb_malloc b LLVM_REQ) nm.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b nm CTX Hnm.
  pose proof CTX as (_ & _ & _ & _ & _ & _ & Hres & Hroom & _).
  exact (lf_room1 A0 b nm Hres Hroom Hnm).
Qed.

Lemma llvm_name_back : forall A b nm,
  res_ok_slots A (sb_free (sb_malloc (sb_malloc b LLVM_REQ) nm) nm) ->
  res_ok_slots A (sb_malloc b LLVM_REQ).
Proof. intros A b nm H. rewrite sb_free_malloc in H. exact H. Qed.

End R.
