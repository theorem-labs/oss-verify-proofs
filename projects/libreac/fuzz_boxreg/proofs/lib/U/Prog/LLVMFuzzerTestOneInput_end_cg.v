From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv
LLVMFuzzerTestOneInput_g LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_link Statement.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_end LLVMFuzzerTestOneInput_cfb read_name_ccf LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_link_cg LLVMFuzzerTestOneInput_gcg.
Import ListNotations.
Local Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : llvm_frame rc B API SH SK.
Hypothesis MCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis LIM : llvm_limlaw B API.

Theorem llvm_contract_of_cases_cf : (llvm_binds B API -> llvm_cases_ok_cf B API) -> LLVMFuzzerTestOneInput_contract_cg B API.
Proof.
  intros CASES.
  apply llvm_g_of_sr_cf. intros BI.
  pose proof FR as (HA & Hel & _).
  exact (LLVMFuzzerTestOneInput_holds_of_cases_cf B API
    (fun fx' => malloc_ag_of_cf B API LIM (MCF fx')) FCF Hel
    (llvm_sink_env rc B API SH SK BI FR) (CASES BI) BI).
Qed.

End E.
