From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import read_name_c LLVMFuzzerTestOneInput_cfb.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition read_name_contract_cf : Prop :=
  forall L A regs mem md c p pl b,
    ms_segs B = rsegs -> ms_malloc B = MALLOC -> errno_addr B + 4 <= alloc_ceiling ->
    call_pre_k B MR (32 + ALLOC_STACK) L A regs mem md -> st_init_done A = true ->
    getr regs 10 = Z_to_bv 64 c -> c mod 8 = 0 -> spZ regs <= c ->
    Mem.bytes_at segs mem c (Mem.le8 (Z_to_bv 64 p) ++ Mem.le8 (Z_to_bv 64 (Z.of_nat (length pl)))) ->
    Mem.wr_at segs mem c 16 ->
    0 <= p < 2 ^ 64 ->
    Mem.bytes_at segs mem p pl ->
    (pl <> [] -> exists a len, In (a, len) (blocks L A) /\ a <= p /\ p + Z.of_nat (length pl) <= a + len) ->
    ro_agree segs mem ->
    res_ok_slots A b -> room_ag b (rn_k pl + 1) ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 READ_NAME) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' s,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         call_post_k B MR (32 + ALLOC_STACK) L A regs mem md (rn_writes c s (rn_k pl)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 s /\
         s <> 0 /\ fresh_block B s (rn_k pl + 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (s, rn_k pl + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         Mem.bytes_at segs mem' s (bsub pl 1 (rn_k pl) ++ [Z_to_bv 8 0]) /\
         Mem.bytes_at segs mem' c
           (Mem.le8 (Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl)) ++
            Mem.le8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         st_init_done A' = true /\
         res_ok_slots A' (sb_malloc b (rn_k pl + 1))).

End K.
