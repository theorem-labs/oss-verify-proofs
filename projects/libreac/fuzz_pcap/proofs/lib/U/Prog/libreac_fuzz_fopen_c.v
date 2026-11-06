From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fmemopen_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LIBREAC_FUZZ_FOPEN : Z := Eval compute in Symbols.Ubsan.s_libreac_fuzz_fopen.
Definition FOPEN_K : Z := 8240.
Definition A_PATH : Z := Eval compute in (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z.
Definition G_FILE_LEN : Z := Eval compute in Symbols.Ubsan.s_g_file_len.

Definition PATH_STR : list byte :=
  [Z_to_bv 8 60; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 45; Z_to_bv 8 105;
   Z_to_bv 8 110; Z_to_bv 8 112; Z_to_bv 8 117; Z_to_bv 8 116; Z_to_bv 8 62].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition fopen_writes (h a : Z) : Prop := h <> 0 /\ fmemopen_writes h a.

Definition libreac_fuzz_fopen_contract : Prop :=
  forall L A regs mem md (pth b : Z) (Fc : list byte) (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR FOPEN_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pth -> pth <> 0 -> bytes_at rsegs mem pth (PATH_STR ++ [Z_to_bv 8 0]) ->
    (pth + 13 <= spZ regs - FOPEN_K \/ spZ regs <= pth) ->
    getr regs 11 = Z_to_bv 64 A_MODE ->
    bytes_at rsegs mem G_FILE_LEN (le8 (wz (Z.of_nat (length Fc))) ++ le8 (wz b)) ->
    Z.of_nat (length Fc) < 2 ^ 26 ->
    ((1 <= length Fc)%nat -> In (b, Z.of_nat (length Fc)) (blocks L A) /\ bytes_at rsegs mem b Fc) ->
    stdio_ok mem -> ofl_empty mem -> guard_ok mem -> ro_agree segs mem ->
    res_ok_slots A b0 -> room_slots b0 1304 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LIBREAC_FUZZ_FOPEN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' h,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR FOPEN_K L A regs mem md (fopen_writes h) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 h /\ stdio_ok mem' /\ guard_ok mem' /\ ro_agree segs mem' /\
         (length Fc = 0%nat ->
            h = 0 /\ L' = L /\ A' = A /\ md' = md /\ Frame.munch [(spZ regs - 32, spZ regs)] mem mem' /\
            ofl_empty mem' /\ res_ok_slots A' b0) /\
         ((1 <= length Fc)%nat ->
            h <> 0 /\ h mod 16 = 0 /\ fresh_block B h 1304 /\
            (exists b1 b2, blocks L' A' = b1 ++ (h, 1304) :: b2 /\ blocks L A = b1 ++ b2) /\
            blocks_kept B L A mem mem' (fun _ => False) /\
            (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
            st_init_done A' = true /\ (length (st_regions A) <= length (st_regions A'))%nat /\
            res_ok_slots A' (sb_malloc b0 1304) /\
            mstl mem' h b Fc 0 (wz 0) (wz 0) /\ ofl_one mem' h)).

End K.
