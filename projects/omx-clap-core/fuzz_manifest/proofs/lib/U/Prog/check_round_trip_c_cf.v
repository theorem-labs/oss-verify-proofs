From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem Ledger ManifestB names_c printf_facts_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free (agreement) twin of check_round_trip_contract (check_round_trip_c.v): SRcf in place of SR, the agreement cap
   (sb_cap b <= CAP_AG) and live bytes after the call at most 2^29 (AgCf.room_ag_of), else unchanged. *)
Section K.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_round_trip_contract_cf : Prop :=
  forall L A regs mem md b (u us : list byte) Lam peak cnt fail,
    segs = rsegs ->
    call_pre_k B MR CRT_K L A regs mem md -> st_init_done A = true ->
    bv_unsigned (getr regs 2) <= TASK_SIZE ->
    frm_zero fp_csr ->
    ro_agree rsegs mem -> guard_cells B mem ->
    cstr_at mem (bv_unsigned (getr regs 10)) u us ->
    (exists a k, In (a, k) (blocks L A) /\ a <= bv_unsigned (getr regs 10) /\
       bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 <= a + k) ->
    (length u <= 255)%nat ->
    img_strings mem -> crt_strings mem ->
    ledger B L A mem Lam peak cnt fail -> quiet cnt fail 1019 ->
    res_ok_slots A b -> sb_live b + 2 <= sb_cap b <= CAP_AG -> 0 <= sb_bytes b ->
    sb_bytes b + (4 * Z.of_nat (length u) + 83) <= 2 ^ 29 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (crt_post B API L A regs mem md u Lam peak cnt b).

End K.
