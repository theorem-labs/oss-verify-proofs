From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem Ledger ManifestB names_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition AS_RULED : Z := 0x13a38.
Definition AS_RULED_K : Z := 32 + NAMES_K.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition as_ruled_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (tb ub : list byte) (Lam : list (Z * Z)) (peak cnt : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ st_init_done A' = true /\
    bpost B MR AS_RULED_K stat_writes L A regs mem md L' A' regs' mem' md' /\
    (exists ts', cstr_at mem' (bv_unsigned (getr regs 10)) tb ts') /\
    (exists us', cstr_at mem' (bv_unsigned (getr regs 11)) ub us') /\
    ( (ub = [] /\ ledger B L' A' mem' Lam peak cnt (2 ^ 64 - 1))
    \/ (ub <> [] /\
        ledger B L' A' mem' Lam (Z.max peak (lsum Lam + Z.of_nat (length ub) + 3)) (cnt + 1) (2 ^ 64 - 1)) ) /\
    res_ok_slots A' b.

Definition as_ruled_contract : Prop :=
  forall L A regs mem md b (tb ts ub us : list byte) Lam peak cnt fail,
    segs = rsegs ->
    call_pre_k B MR AS_RULED_K L A regs mem md -> st_init_done A = true ->
    bv_unsigned (getr regs 2) <= TASK_SIZE ->
    frm_zero fp_csr ->
    ro_agree rsegs mem -> guard_cells B mem ->
    cstr_at mem (bv_unsigned (getr regs 10)) tb ts ->
    cstr_at mem (bv_unsigned (getr regs 11)) ub us ->
    str_home L A (bv_unsigned (getr regs 10)) (Z.of_nat (length tb + 1)) ->
    str_home L A (bv_unsigned (getr regs 11)) (Z.of_nat (length ub + 1)) ->
    4096 <= bv_unsigned (getr regs 10) -> 4096 <= bv_unsigned (getr regs 11) ->
    Z.of_nat (length tb) + 1 < 2 ^ 62 -> (length ub <= 255)%nat ->
    img_strings mem ->
    off_stack (getr regs 2) AS_RULED_K (bv_unsigned (getr regs 10)) (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack (getr regs 2) AS_RULED_K (bv_unsigned (getr regs 11)) (Z.of_nat (length ub + 1 + length us)) ->
    off_statics (bv_unsigned (getr regs 10)) (Z.of_nat (length tb + 1 + length ts)) ->
    off_statics (bv_unsigned (getr regs 11)) (Z.of_nat (length ub + 1 + length us)) ->
    ledger B L A mem Lam peak cnt fail ->
    quiet cnt fail 1 ->
    res_ok_slots A b -> sb_live b + 1 <= sb_cap b <= CAPMAX -> 0 <= sb_bytes b ->
    sb_bytes b + (Z.of_nat (length ub) + 19) <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 AS_RULED) mem (seg_rom segs)) md)
      (as_ruled_post L A regs mem md tb ub Lam peak cnt b).

End K.
