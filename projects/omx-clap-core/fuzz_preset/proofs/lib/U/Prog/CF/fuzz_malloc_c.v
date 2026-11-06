From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan (sha256
   27566683...), whose SHF_ALLOC sections equal those of the pinned fuzz_preset.ubsan 45b0357d... except .note.gnu.build-id:
     fuzz_malloc  FUNC   GLOBAL 0x15adc size 284
     g_ran_out    OBJECT LOCAL  0x35258 size 1  (static int g_ran_out is kept as one byte: sb at 0x15bd8)
   #102 (alloc.c refused()): a refusal raises g_peak and sets g_ran_out only when n <= g_most. Both refusal arms stay
   outside this contract: TOOBIG (0x15b2c bltu -17, n) by n + 16 <= 2 ^ 30, REFUSED (0x15b38 beqz a0) by rf_room. *)
Definition FUZZ_MALLOC : Z := 0x15adc.
Definition G_RAN_OUT : Z := 0x35258.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition alloc_writes (res a : Z) : Prop :=
  alloc_statics a \/ (res <> 0 /\ res - 16 <= a < res).

Definition fuzz_malloc_contract : Prop :=
  forall L A regs mem md n b Lam peak cnt fail,
    call_pre_k B MR (ALLOC_STACK + 32) L A regs mem md ->
    getr regs 10 = Z_to_bv 64 n -> 0 <= n ->
    ledger B L A mem Lam peak cnt fail ->
    ro_agree segs mem ->
    rf_ok F A b -> rf_room F b (n + 16) -> n + 16 <= 2 ^ 30 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FUZZ_MALLOC) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (st_init_done A' = false -> forall i, 0 <= i < 8 -> mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
         call_post_k B MR (ALLOC_STACK + 32) L A regs mem md (alloc_writes res) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         getr regs' 10 = Z_to_bv 64 res /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         (* g_ran_out keeps its value on every arm: its one store (0x15bd8 sb a1, 0(s1), a1 = 1) is inside refused()
            (0x15ba0-0x15bd8), which runs only after a NULL from libc malloc (0x15b38 beqz a0) or on TOOBIG (0x15b2c);
            the precondition rf_room F b (n + 16) at line 42 makes libc malloc return non-NULL (malloc_contract_r,
            lib/U/Contract.v:170 res <> 0), and n + 16 <= 2 ^ 30 excludes TOOBIG. *)
         mbyte segs mem' G_RAN_OUT = mbyte segs mem G_RAN_OUT /\
         ( (cnt = fail /\ res = 0 /\ L' = L /\ A' = A /\ md' = md /\ rf_ok F A' b /\
            writes_only B (fun a => alloc_statics a \/ bv_unsigned (getr regs 2) - (ALLOC_STACK + 32) <= a < bv_unsigned (getr regs 2)) mem mem' /\
            blocks L' A' = blocks L A /\
            ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1))
         \/ (cnt <> fail /\ res <> 0 /\ res mod 16 = 0 /\ rf_ok F A' (rf_malloc F b (n + 16)) /\
            (forall i, 0 <= i < n + 16 -> ~ alloc_statics (res - 16 + i)) /\
            (forall i, 0 <= i < n + 16 -> ~ in_img B (res - 16 + i)) /\ ~ In res (map fst Lam) /\
            (exists b1 b2, blocks L' A' = b1 ++ (res - 16, n + 16) :: b2 /\ blocks L A = b1 ++ b2) /\
            ledger B L' A' mem' ((res, n) :: Lam) (Z.max peak (lsum Lam + n)) ((cnt + 1) mod 2 ^ 64) fail) )).

End K.
