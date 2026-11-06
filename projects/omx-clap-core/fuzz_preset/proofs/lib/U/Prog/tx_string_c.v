From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import tx_put_c TxRet Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
Import ListNotations.
Local Open Scope Z_scope.

Definition TX_STRING : Z := 0x158d4.
Definition TS_STACK : Z := 112 + TX_STACK.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition tx_string_contract : Prop :=
  forall L A regs mem md (t s k b0 len0 cap0 : Z) (bs : list Z) (txt : list byte) (bnd : rf_R F)
         (Lam : list (Z * Z)) (peak cnt fail : Z),
    let add := map (Z_to_bv 8) (wstr bs) in
    let lb := fun a n => In (a, n) Lam in
    tx_start B API F TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) (len0 + Z.of_nat (length add) + 1) ->
    getr regs 11 = Z_to_bv 64 s ->
    ledger B L A mem Lam peak cnt fail ->
    pj_cstr segs mem lb s k bs ->
    (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 TX_STRING) mem (seg_rom segs)) md)
      (tx_ret B API F TS_STACK L A regs mem md t b0 len0 cap0 txt add (plen (strp bs)) bnd
         (fun L' A' mem' => ledger B L' A' mem' Lam peak cnt fail /\ pj_cstr segs mem' lb s k bs)).

End K.
