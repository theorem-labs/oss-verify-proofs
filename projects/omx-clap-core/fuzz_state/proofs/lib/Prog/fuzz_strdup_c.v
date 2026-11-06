From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_STRDUP : Z := 0x1416c.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition strdup_writes (res a : Z) : Prop :=
  alloc_statics a \/ (res <> 0 /\ res - 16 <= a < res).

Definition fuzz_strdup_contract : Prop :=
  forall L A regs mem md s cs slack b Lam peak cnt fail,
    call_pre_k B MR (ALLOC_STACK + 64) L A regs mem md ->
    getr regs 10 = Z_to_bv 64 s ->
    Mem.bytes_at segs mem s (cs ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) cs ->
    (- (s + Z.of_nat (length cs) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (forall a, s <= a < s + Z.of_nat (length cs) + 1 -> ~ (bv_unsigned (getr regs 2) - (ALLOC_STACK + 64) <= a < bv_unsigned (getr regs 2))) ->
    (forall a, s <= a < s + Z.of_nat (length cs) + 1 ->
       bv_unsigned (getr regs 2) <= a \/ Mem.ro_addr segs (Z_to_bv 64 a) = true \/
       exists p k, In (p, k) (blocks L A) /\ p <= a < p + k) ->
    ledger B L A mem Lam peak cnt fail ->
    ro_agree segs mem ->
    rf_ok F A b -> rf_room F b (Z.of_nat (length cs) + 17) -> Z.of_nat (length cs) + 17 <= 2 ^ 30 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FUZZ_STRDUP) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (st_init_done A' = false -> forall i, 0 <= i < 8 -> mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
         call_post_k B MR (ALLOC_STACK + 64) L A regs mem md (strdup_writes res) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         getr regs' 10 = Z_to_bv 64 res /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         ( (cnt = fail /\ res = 0 /\ L' = L /\ A' = A /\ md' = md /\ rf_ok F A' b /\
            writes_only B (fun a => alloc_statics a \/ bv_unsigned (getr regs 2) - (ALLOC_STACK + 64) <= a < bv_unsigned (getr regs 2)) mem mem' /\
            blocks L' A' = blocks L A /\
            ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1))
         \/ (cnt <> fail /\ res <> 0 /\ res mod 16 = 0 /\ rf_ok F A' (rf_malloc F b (Z.of_nat (length cs) + 17)) /\
            (forall i, 0 <= i < Z.of_nat (length cs) + 1 + 16 -> ~ alloc_statics (res - 16 + i)) /\
            (forall i, 0 <= i < Z.of_nat (length cs) + 1 + 16 -> ~ in_img B (res - 16 + i)) /\ ~ In res (map fst Lam) /\
            Mem.bytes_at segs mem' res (cs ++ [Z_to_bv 8 0]) /\
            (exists b1 b2, blocks L' A' = b1 ++ (res - 16, Z.of_nat (length cs) + 17) :: b2 /\ blocks L A = b1 ++ b2) /\
            ledger B L' A' mem' ((res, Z.of_nat (length cs) + 1) :: Lam)
              (Z.max peak (lsum Lam + Z.of_nat (length cs) + 1)) ((cnt + 1) mod 2 ^ 64) fail) )).

End K.
