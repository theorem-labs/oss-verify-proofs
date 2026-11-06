From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract MemNorm AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import HStateRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require ReaderRes strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Module URR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.ReaderRes.
Module UST := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_ROUND_TRIP : Z := 0x139ac.
(* ubsan: frame 352 + pj_parse K 14160 (U PARSE_ITEMS_F 96) needs 14512; rounded up. *)
Definition CRT_STK : Z := ALLOC_STACK + 6400.
Definition CRT_ALLOCS : Z := 68.
Definition CRT_OPS : nat := 160.
Definition CRT_SIZE : Z := 2 ^ 25.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_round_trip_contract : Prop :=
  forall L A regs mem md t tb slack bd bs bnd Lam peak cnt,
    call_pre_k B MR CRT_STK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 bd ->
    getr regs 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    Mem.bytes_at segs mem t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
    (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
    Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
    (forall a, t <= a < t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) ->
       ~ in_window (spZ regs) CRT_STK a) ->
    (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
    b64_dec (zs tb) = Some bs -> bd <> 0 ->
    Mem.bytes_at segs mem bd (bz bs) ->
    (exists k, In (bd, k) Lam /\ Z.of_nat (length bs) <= k) ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 ->
    URR.rd_cells B mem -> spZ regs <= 2 ^ 47 -> UST.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
    frm_zero fp_csr ->
    res_ok_slots A bnd -> hs_cap bnd CRT_OPS CRT_SIZE ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YK11.FPState) L' A' regs' mem' md' peak' cnt',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         URR.fregs_kept fx fx' /\
         frm_zero (@fp_csr fx') /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         call_post_k B MR CRT_STK L A regs mem md alloc_statics L' A' regs' mem' md' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         peak <= peak' /\ cnt <= cnt' <= cnt + CRT_ALLOCS /\
         ledger B L' A' mem' Lam peak' cnt' (2 ^ 64 - 1) /\
         res_ok_slots A' bnd).

End K.
