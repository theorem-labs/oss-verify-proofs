From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256
   c8f4d6b8...), whose SHF_ALLOC sections equal those of the pinned fuzz_preset.plain 805604bb... except .note.gnu.build-id:
     fuzz_realloc FUNC   GLOBAL 0x15564 size 572
     g_ran_out    OBJECT LOCAL  0x347a8 size 1  (static int g_ran_out is kept as one byte: sb at 0x15618 and 0x15724)
   #102 (alloc.c refused()): a refusal raises g_peak and sets g_ran_out only when n <= g_most. Both refusal arms stay
   outside this contract: TOOBIG (0x155e4 bltu n, -16 not taken) by n + 16 <= 2 ^ 30, REFUSED (0x15694 beqz a0)
   by rf_room. *)
Definition FUZZ_REALLOC : Z := 0x15564.
Definition G_RAN_OUT : Z := 0x347a8.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition realloc_writes (p k res a : Z) : Prop :=
  alloc_statics a \/ (p <> 0 /\ p - 16 <= a < p + k) \/ (res <> 0 /\ res - 16 <= a < res).

Definition fuzz_realloc_contract : Prop :=
  forall L A regs mem md p k n old b Lam peak cnt fail,
    call_pre_k B MR (REALLOC_STACK + 48) L A regs mem md ->
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= n ->
    ledger B L A mem Lam peak cnt fail ->
    ro_agree segs mem ->
    (p = 0 /\ k = 0 \/ In (p, k) Lam) ->
    Z.of_nat (length old) = k ->
    (forall i, 0 <= i < k -> mbyte segs mem (p + i) = nth_error old (Z.to_nat i)) ->
    rf_ok F A b -> rf_room F b (n + 16) -> n + 16 <= 2 ^ 30 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FUZZ_REALLOC) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (st_init_done A' = false -> forall i, 0 <= i < 8 -> mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
         call_post_k B MR (REALLOC_STACK + 48) L A regs mem md (realloc_writes p k res) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         getr regs' 10 = Z_to_bv 64 res /\
         (* g_ran_out keeps its value on every arm: its two stores here are inside the inlined refused() (0x15618 on
            TOOBIG, 0x15724 after a NULL from libc realloc at 0x15694 beqz a0); n + 16 <= 2 ^ 30 excludes TOOBIG and the
            precondition rf_room F b (n + 16) at line 45 makes libc realloc return non-NULL (realloc_contract_r,
            lib/Contract.v:214 res <> 0); the p = 0 arm is the tail call to fuzz_malloc (0x155dc), whose contract states
            the same. *)
         mbyte segs mem' G_RAN_OUT = mbyte segs mem G_RAN_OUT /\
         ( (cnt = fail /\ res = 0 /\ L' = L /\ A' = A /\ md' = md /\ rf_ok F A' b /\
            writes_only B (fun a => alloc_statics a \/ bv_unsigned (getr regs 2) - (REALLOC_STACK + 48) <= a < bv_unsigned (getr regs 2)) mem mem' /\
            blocks L' A' = blocks L A /\ keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
            ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1))
         \/ (cnt <> fail /\ res <> 0 /\ res mod 16 = 0 /\
            (forall i, 0 <= i < n + 16 -> ~ alloc_statics (res - 16 + i)) /\
            (forall i, 0 <= i < n + 16 -> ~ in_img B (res - 16 + i)) /\ keeps B L A mem mem' (p - 16) /\ ublocks_kept L A A' (p - 16, k + 16) /\
            (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
            exists l1 l2,
              (p = 0 /\ l1 = [] /\ l2 = Lam /\ rf_ok F A' (rf_malloc F b (n + 16))
                 /\ (exists b1 b2, blocks L' A' = b1 ++ (res - 16, n + 16) :: b2 /\ blocks L A = b1 ++ b2)
               \/ p <> 0 /\ Lam = l1 ++ (p, k) :: l2 /\ rf_ok F A' (rf_realloc F b (k + 16) (n + 16))
                 /\ (exists b1 b2 c1 c2, blocks L A = b1 ++ (p - 16, k + 16) :: b2
                                  /\ blocks L' A' = c1 ++ (res - 16, n + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)) /\
              ~ In res (map fst (l1 ++ l2)) /\
              ledger B L' A' mem' ((res, n) :: l1 ++ l2) (Z.max peak (lsum (l1 ++ l2) + n))
                ((cnt + 1) mod 2 ^ 64) fail) )).

End K.
