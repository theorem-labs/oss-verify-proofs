From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger WriterSpec HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import HStateRoom check_as_written_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_REJECT_CLEAN_STARVED : Z := 0x13d84.
Definition CRCS_FRAME : Z := 48.
Definition CRCS_STK : Z := ALLOC_STACK + 1024.

Definition starved_ops (n bd l : Z) : list hop :=
  HMal (n / 4 * 3 + 3 + 16) :: (if Z.eqb bd 0 then [] else [HMal ((l + 2) / 3 * 4 + 1 + 16)]).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_reject_clean_starved_contract : Prop :=
  forall L A regs mem md t tb slack bd l bnd Lam peak cnt,
    call_pre_k B MR CRCS_STK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 bd -> getr regs 12 = Z_to_bv 64 l ->
    Mem.bytes_at segs mem t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
    (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
    Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
    (forall a, t <= a < t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) ->
       ~ in_window (spZ regs) CRCS_STK a) ->
    (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
    caw_answer B mem tb bd l ->
    (bd <> 0 -> exists k, In (bd, k) Lam /\ l <= k) ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + 2 < 2 ^ 63 ->
    ro_agree segs mem ->
    res_ok_slots A bnd -> hs_room bnd (starved_ops (Z.of_nat (length tb)) bd l) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_REJECT_CLEAN_STARVED) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         call_post_k B MR CRCS_STK L A regs mem md alloc_statics L' A' regs' mem' md' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         blocks L' A' = blocks L A /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         ledger B L' A' mem' Lam peak (if Z.eqb bd 0 then cnt + 1 else cnt + 2) (2 ^ 64 - 1) /\
         res_ok_slots A' bnd).

End K.
