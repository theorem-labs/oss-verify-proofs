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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem Ledger ManifestB.
Import ListNotations.
Local Open Scope Z_scope.

Definition NAMES : Z := 0x13c1c.
Definition READINGS : Z := 0x13c3c.
Definition READINGS_KB : Z := 176 + (ALLOC_STACK + 32).
Definition NAMES_K : Z := 16 + READINGS_KB.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition str_home (L : layout) (A : astate) (s n : Z) : Prop :=
  (exists a k, In (a, k) (blocks L A) /\ a <= s /\ s + n <= a + k) \/
  (forall i, 0 <= i < n -> ro_addr rsegs (Z_to_bv 64 (s + i)) = true).

Definition names_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (K : Z) (tb ub : list byte) (Lam : list (Z * Z)) (peak cnt fail : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md' res,
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ st_init_done A' = true /\
    bpost B MR K stat_writes L A regs mem md L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 res /\
    (exists ts', cstr_at mem' (bv_unsigned (getr regs 10)) tb ts') /\
    (exists us', cstr_at mem' (bv_unsigned (getr regs 11)) ub us') /\
    ( (ub = [] /\ res = 0 /\ ledger B L' A' mem' Lam peak cnt fail)
    \/ (ub <> [] /\ cnt = fail /\ res = 0 /\
        ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1))
    \/ (ub <> [] /\ cnt <> fail /\ res = names (zbytes tb) (zbytes ub) /\
        ledger B L' A' mem' Lam (Z.max peak (lsum Lam + Z.of_nat (length ub) + 3))
          ((cnt + 1) mod 2 ^ 64) fail) ) /\
    res_ok_slots A' b.

Definition names_contract : Prop :=
  forall L A regs mem md b (tb ts ub us : list byte) Lam peak cnt fail,
    segs = rsegs ->
    call_pre_k B MR NAMES_K L A regs mem md -> st_init_done A = true ->
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
    off_stack (getr regs 2) NAMES_K (bv_unsigned (getr regs 10)) (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack (getr regs 2) NAMES_K (bv_unsigned (getr regs 11)) (Z.of_nat (length ub + 1 + length us)) ->
    off_stack (getr regs 2) NAMES_K PREFIX_LC_STR 7 ->
    off_stack (getr regs 2) NAMES_K PREFIX_UC_STR 7 ->
    off_stack (getr regs 2) NAMES_K FMT_WHOLE_STR 5 ->
    off_statics (bv_unsigned (getr regs 10)) (Z.of_nat (length tb + 1 + length ts)) ->
    off_statics (bv_unsigned (getr regs 11)) (Z.of_nat (length ub + 1 + length us)) ->
    ledger B L A mem Lam peak cnt fail ->
    res_ok_slots A b -> sb_live b + 1 <= sb_cap b <= CAPMAX -> 0 <= sb_bytes b ->
    sb_bytes b + (Z.of_nat (length ub) + 19) <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 NAMES) mem (seg_rom segs)) md)
      (names_post L A regs mem md NAMES_K tb ub Lam peak cnt fail b).

End K.
