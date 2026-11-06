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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import HStateRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_NO_OVERREAD : Z := 0x13440.
Definition CNO_STK : Z := ALLOC_STACK + 1024.

Definition nor_ops (n : Z) (ok : bool) : list hop :=
  [HMal (n + 18); HMal (n + 18); HMal (n + 18)] ++
  dec_ops ok n ++ dec_ops ok n ++ dec_ops ok n ++
  dec_free_ops ok n ++ dec_free_ops ok n ++ dec_free_ops ok n ++
  [HFre (n + 18); HFre (n + 18); HFre (n + 18)].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_no_overread_contract : Prop :=
  forall L A regs mem md d (db : list byte) bnd Lam peak cnt,
    call_pre_k B MR CNO_STK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length db)) ->
    Mem.bytes_at segs mem d db -> ~ In (Z_to_bv 8 0) db ->
    Z.of_nat (length db) <= 3 * 2 ^ 20 ->
    (0 < Z.of_nat (length db) ->
       exists pd k, In (pd, k) (blocks L A) /\ pd <= d /\ d + Z.of_nat (length db) <= pd + k) ->
    (forall a, d <= a < d + Z.of_nat (length db) -> ~ in_window (spZ regs) CNO_STK a) ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + 3 < 2 ^ 63 ->
    ro_agree segs mem ->
    res_ok_slots A bnd ->
    hs_room bnd (nor_ops (Z.of_nat (length db)) (opt_ok (b64_dec (zs db)))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' peak',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         call_post_k B MR CNO_STK L A regs mem md alloc_statics L' A' regs' mem' md' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         blocks L' A' = blocks L A /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         peak <= peak' /\
         ledger B L' A' mem' Lam peak' (cnt + 3) (2 ^ 64 - 1) /\
         res_ok_slots A' bnd).

End K.
