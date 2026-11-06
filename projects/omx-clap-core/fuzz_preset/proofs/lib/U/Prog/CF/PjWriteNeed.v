From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import put_c WriterRet write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Definition pj_write_need (KW : Z) : Prop :=
  forall L A regs mem md b v pretty (t : jv) D Lam peak cnt fail,
    ms_segs B = rsegs -> ms_got_guard B = snprintf_c.GOT_GUARD -> ms_guard B = snprintf_c.GUARD ->
    call_pre_t B API KW L A regs mem md -> st_init_done A = true ->
    ro_agree (ms_segs B) mem -> frm0 (@fp_csr fx) ->
    getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 pretty -> 0 <= pretty < 2 ^ 64 ->
    ledger B L A mem Lam peak cnt fail ->
    off_errno B (spZ regs - KW) KW ->
    pj_node rsegs mem (wv_lblk Lam) v t D -> pjw_where B regs Lam v ->
    (forall a k, In (a, k) D -> In (a, k) Lam) ->
    Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 -> (PjTree.depth t <= 32)%nat ->
    Z.of_nat (length (wdoc t (negb (pretty =? 0)))) + 1 <= WMAX ->
    rf_ok RF A b -> wr_rooms RF b (w0 cnt fail) (wdpieces t (negb (pretty =? 0))) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE_PC) mem (seg_rom (ms_segs B))) md)
      (pj_write_ret B API RF KW L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b).

End K.
