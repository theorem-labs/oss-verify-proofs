From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition XMALLOC : Z := 0x15a88.
Definition XMALLOC_K : Z := ALLOC_STACK + 16.

Definition xmalloc_size (n : Z) : Z := if n =? 0 then 1 else n.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition xmalloc_contract : Prop :=
  forall L A regs mem md (n : Z) b,
    call_pre_k B MR XMALLOC_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 n -> 0 <= n <= LMAX + 2 ->
    res_ok_slots A b -> room_ag (sb_malloc b (xmalloc_size n)) (xmalloc_size n) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 XMALLOC) mem (seg_rom segs)) md)
      (malloc_ret B API XMALLOC_K L A regs mem md (xmalloc_size n) b).

End K.
