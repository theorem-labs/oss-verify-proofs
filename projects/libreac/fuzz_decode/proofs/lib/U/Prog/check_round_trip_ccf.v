From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_braid_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_round_trip_contract_cf : Prop :=
  forall L A regs mem md (audio pcm nch ns : Z) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CRT_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 audio -> getr regs 11 = Z_to_bv 64 pcm ->
    getr regs 12 = Z_to_bv 64 nch -> getr regs 13 = Z_to_bv 64 ns ->
    Z.even nch = true -> 2 <= nch <= 127 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
    0 < audio < 2 ^ 63 -> 0 < pcm < 2 ^ 63 ->
    in_block L A audio (3 * nch * ns) -> in_block L A pcm (3 * nch * ns) ->
    braid_map mem audio pcm nch ns ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A b ->
    (sb_live b + 3 <= sb_cap b <= CAP_AG /\ 128 <= sb_cap b) /\ 0 <= sb_bytes b /\ sb_bytes b + 7 * nch * ns + 8 * nch <= 2 ^ 29 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
