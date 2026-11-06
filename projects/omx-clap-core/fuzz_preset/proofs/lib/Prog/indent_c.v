From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import put_c WriterRet.
Import ListNotations.
Local Open Scope Z_scope.

Definition INDENT_PC : Z := 0x16cbc.
Definition IND_K : Z := 32 + PUT_K.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Definition indent_contract : Prop :=
  forall L A regs mem md b o pretty depth buf (st : wst) Lam peak,
    ms_segs B = rsegs ->
    call_pre_k B (aa_MR API) IND_K L A regs mem md -> st_init_done A = true ->
    ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 pretty -> getr regs 12 = Z_to_bv 64 depth ->
    0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
    pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) ->
    ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
    spZ regs <= o -> off_errno B o 32 -> off_errno B (spZ regs - IND_K) IND_K ->
    Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (wind (negb (pretty =? 0)) depth))) + 1 <= WMAX ->
    rf_ok RF A b -> wr_rooms RF b st (wind (negb (pretty =? 0)) depth) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 INDENT_PC) mem (seg_rom (ms_segs B))) md)
      (wr_ret B API RF IND_K L A regs mem md o buf st Lam peak b (wind (negb (pretty =? 0)) depth)).

End K.
