From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
tx_put_c TxRet tx_string_c WriterValue Ledger PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import TxCalls.
Import ListNotations.
Local Open Scope Z_scope.

Definition TX_VALUE : Z := 0x14fc0.
Definition TV_F : Z := 112.
Definition TV_K (tv : jv) : Z := TV_F * (Z.of_nat (depth tv) + 1) + TS_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition tx_value_contract : Prop :=
  forall L A regs mem md (t v pretty d b0 len0 cap0 : Z) (tv : jv) (D : list (Z * Z)) (txt : list byte)
         (bnd : rf_R F) (Lam : list (Z * Z)) (peak cnt fail : Z),
    let p := negb (pretty =? 0) in
    let add := map (Z_to_bv 8) (concat (wvpieces tv p d)) in
    let lb := fun a n => In (a, n) Lam in
    tx_start B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd (tv_calls tv p d) (len0 + Z.of_nat (length add) + 1) ->
    getr regs 11 = Z_to_bv 64 v -> getr regs 12 = Z_to_bv 64 pretty -> getr regs 13 = Z_to_bv 64 d ->
    - 2 ^ 31 <= pretty < 2 ^ 31 -> 0 <= d -> d + Z.of_nat (depth tv) <= 2 ^ 31 - 1 ->
    ledger B L A mem Lam peak cnt fail ->
    pj_node segs mem lb v tv D ->
    (forall b, In b D -> In b Lam) ->
    (spZ regs <= v \/ exists a n, In (a, n) Lam /\ a <= v /\ v + 56 <= a + n) ->
    v + 56 <= 2 ^ 64 -> (v + 56 <= t \/ t + 24 <= v) ->
    (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 TX_VALUE) mem (seg_rom segs)) md)
      (tx_ret B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt add (tv_calls tv p d) bnd
         (fun L' A' mem' => ledger B L' A' mem' Lam peak cnt fail /\ pj_node segs mem' lb v tv D /\
            forall x, pj_foot v D x -> mbyte segs mem' x = mbyte segs mem x)).

End K.
