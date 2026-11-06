From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition PAST_NUL : Z := 0x13e38.
Definition PAST_NUL_FRAME : Z := 48.

Definition pn_copy (db : list byte) (c : Z) : list byte :=
  db ++ [Z_to_bv 8 0; Z_to_bv 8 (c mod 256); Z_to_bv 8 65] ++ repeat (Z_to_bv 8 0) 15.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition past_nul_contract : Prop :=
  forall L A regs mem md d n c (db : list byte) b Lam peak cnt fail,
    call_pre_k B MR (ALLOC_STACK + PAST_NUL_FRAME) L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 c ->
    0 <= c < 2 ^ 64 ->
    0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n ->
    (forall i, 0 <= i < n -> mbyte segs mem (d + i) = nth_error db (Z.to_nat i)) ->
    (0 < n -> exists pd k, In (pd, k) (blocks L A) /\ pd <= d /\ d + n <= pd + k) ->
    ledger B L A mem Lam peak cnt fail ->
    res_ok_slots A b -> room_slots b (n + 18) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PAST_NUL) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR (ALLOC_STACK + PAST_NUL_FRAME) L A regs mem md
           (fun a => res <= a < res + n + 18) L' A' regs' mem' md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\ st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         getr regs' 10 = Z_to_bv 64 res /\
         res <> 0 /\ res mod 16 = 0 /\ fresh_block B res (n + 18) /\
         (exists b1 b2, blocks L' A' = b1 ++ (res, n + 18) :: b2 /\ blocks L A = b1 ++ b2) /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         (forall i, 0 <= i < n + 18 -> mbyte segs mem' (res + i) = nth_error (pn_copy db c) (Z.to_nat i)) /\
         ledger B L' A' mem' Lam peak cnt fail /\
         res_ok_slots A' (sb_malloc b (n + 18))).

End K.
