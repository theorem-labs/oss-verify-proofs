From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem Ledger ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf check_no_overread_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free (agreement) twin of check_no_overread_contract (check_no_overread_c.v): SRcf in place of SR, the agreement cap
   (sb_cap b <= CAP_AG) and live bytes after the call at most 2^29 (AgCf.room_ag_of), else unchanged. *)
Section K.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_no_overread_contract_cf : Prop :=
  forall L A regs mem md b (ub tb : list byte) Lam peak cnt fail,
    segs = rsegs ->
    call_pre_k B MR CNO_K L A regs mem md -> st_init_done A = true ->
    bv_unsigned (getr regs 2) <= TASK_SIZE ->
    frm_zero fp_csr ->
    ro_agree rsegs mem ->
    getr regs 11 = Z_to_bv 64 (Z.of_nat (length ub)) ->
    getr regs 13 = Z_to_bv 64 (Z.of_nat (length tb)) ->
    bytes_at rsegs mem (bv_unsigned (getr regs 10)) ub ->
    bytes_at rsegs mem (bv_unsigned (getr regs 12)) tb ->
    Forall (fun x => bv_unsigned x <> 0) ub -> Forall (fun x => bv_unsigned x <> 0) tb ->
    (length ub <= 255)%nat -> Z.of_nat (length tb) <= 2 ^ 22 ->
    in_blk (blocks L A) (bv_unsigned (getr regs 10)) (Z.of_nat (length ub)) ->
    in_blk (blocks L A) (bv_unsigned (getr regs 12)) (Z.of_nat (length tb)) ->
    img_strings mem ->
    ledger B L A mem Lam peak cnt fail -> quiet cnt fail 2 ->
    res_ok_slots A b -> sb_live b + 5 <= sb_cap b <= CAP_AG -> 0 <= sb_bytes b ->
    sb_bytes b + (3 * Z.of_nat (length ub) + 2 * Z.of_nat (length tb) + 91) <= 2 ^ 29 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom segs)) md)
      (cno_post B API L A regs mem md ub tb Lam peak cnt fail b).

End K.
