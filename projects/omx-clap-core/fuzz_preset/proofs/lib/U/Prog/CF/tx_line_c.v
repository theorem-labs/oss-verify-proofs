From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition TX_LINE : Z := 0x15a70.
Definition TL_STACK : Z := 32 + TX_STACK.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition tx_line_contract : Prop :=
  forall L A regs mem md (t d b0 len0 cap0 : Z) (txt : list byte) (bnd : rf_R F),
    let add := map (Z_to_bv 8) (concat (wind true d)) in
    tx_start B API F TL_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (wind true d)) (len0 + 1 + 2 * d + 1) ->
    getr regs 11 = Z_to_bv 64 d -> 0 <= d <= 2 ^ 31 - 1 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 TX_LINE) mem (seg_rom segs)) md)
      (tx_ret B API F TL_STACK L A regs mem md t b0 len0 cap0 txt add (plen (wind true d)) bnd (fun _ _ _ => True)).

End K.
