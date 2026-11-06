From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_FREE : Z := 0x14378.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition free_writes (p k a : Z) : Prop :=
  G_LIVE <= a < G_LIVE + 8 \/ (p <> 0 /\ p - 16 <= a < p + k).

Definition fuzz_free_contract : Prop :=
  forall L A regs mem md p k b Lam peak cnt fail,
    call_pre_k B MR ALLOC_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 p ->
    ledger B L A mem Lam peak cnt fail ->
    ro_agree segs mem ->
    (p = 0 /\ k = 0 \/ In (p, k) Lam) ->
    rf_ok F A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FUZZ_FREE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (st_init_done A' = false -> forall i, 0 <= i < 8 -> mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
         call_post_k B MR ALLOC_STACK L A regs mem md (free_writes p k) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         keeps B L A mem mem' (p - 16) /\ ublocks_kept L A A' (p - 16, k + 16) /\
         ( (p = 0 /\ L' = L /\ A' = A /\ regs' = regs /\ mem' = mem /\ md' = md /\ blocks L' A' = blocks L A /\ ledger B L' A' mem' Lam peak cnt fail /\ rf_ok F A' b)
         \/ (p <> 0 /\
            (exists b1 b2, blocks L A = b1 ++ (p - 16, k + 16) :: b2 /\ blocks L' A' = b1 ++ b2) /\
            (exists l1 l2, Lam = l1 ++ (p, k) :: l2 /\ ledger B L' A' mem' (l1 ++ l2) peak cnt fail) /\
            rf_ok F A' (rf_free F b (k + 16))) )).

End K.
