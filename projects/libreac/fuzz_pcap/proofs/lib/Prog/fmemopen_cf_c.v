From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract AllocSlots SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fmemopen_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition fmemopen_contract_cf : Prop :=
  forall L A regs mem md (b : Z) (Fc : list byte) (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR FMEMOPEN_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length Fc)) ->
    getr regs 12 = Z_to_bv 64 A_MODE ->
    In (b, Z.of_nat (length Fc)) (blocks L A) -> (1 <= length Fc)%nat ->
    bytes_at rsegs mem b Fc ->
    stdio_ok mem -> ofl_empty mem -> guard_ok mem -> ro_agree segs mem ->
    res_ok_slots A b0 -> room_cf md b0 1304 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 FMEMOPEN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' h,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR FMEMOPEN_K L A regs mem md (fmemopen_writes h) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 h /\ h <> 0 /\ h mod 16 = 0 /\ fresh_block B h 1304 /\
         (exists b1 b2, blocks L' A' = b1 ++ (h, 1304) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
         st_init_done A' = true /\ (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b0 1304) /\
         mstl mem' h b Fc 0 (wz 0) (wz 0) /\ ofl_one mem' h /\ stdio_ok mem' /\ guard_ok mem' /\ ro_agree segs mem').

End K.
