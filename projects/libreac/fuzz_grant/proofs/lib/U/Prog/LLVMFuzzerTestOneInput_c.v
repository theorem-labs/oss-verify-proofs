From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import FrameAPI.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x1313c.
Definition LLVM_FRAME : Z := 608.
Definition LLVM_STACK : Z := LLVM_FRAME + ALLOC_STACK.

Definition CTRL_HEADAMP_ROW : Z := 0x1ee20.
Definition CTRL_HEADAMP_BYTES : list byte :=
  map (Z_to_bv 8)
    [0xcd; 0xea; 0x02; 0x00; 0x00; 0x00; 0x00; 0x00; 0x94; 0x05; 0x01; 0x00;
     0x00; 0x00; 0x00; 0x00; 0x12; 0x03; 0x10; 0x06; 0x02; 0x02; 0x00; 0x00].

Definition G_grant : list (Z * Z) := [].
Definition GI_grant (j : nat) (mem : word -> option byte) : Prop := True.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition LLVMFuzzerTestOneInput_contract : Prop :=
  forall ra empty stk : Z, LLVM_STACK <= stk ->
  forall j : nat, (j < 4)%nat ->
    lib_contract_g B API G_grant frame_RELRO GI_grant j LLVM_ENTRY ra empty stk.

End K.
